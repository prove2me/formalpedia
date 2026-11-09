-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_20
-- name    : RobustFracMP.claim_3_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:58:56.247917+00:00
-- url     : https://prove2.me/theorems/77bc4bf4-ae05-4b1f-a44d-770427c7f5ce
-- title:
--   Claim 3.20 — far pairs
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\beta^*=2^{-z-1}$ and $y^{(\beta^*)}=r^{(\beta^*)}/\lambda$. Let $x$ be a feasible assignment for $y^{(\beta^*)}$ ($x\sim y^{(\beta^*)}$) that is optimal, $\sigma_z(x)=\mathrm{cost}_z(y^{(\beta^*)})$, and let $\tilde y\in\mathbb R^P_{\ge0}$. With the far pairs
--
--   $$\mathcal F=\Bigl\{(p,q)\in P\times P:\ \beta^*\,\mathrm{dist}^z(p,q)>\frac1{3\cdot2^{z-1}}\,r^{(\beta^*)}_p\Bigr\},$$
--
--   $$\sum_{(p,q)\in\mathcal F}[x_{p,q}-\tilde y_q]_+\cdot r^{(\beta^*)}_p\le\frac34\,\mathrm{cost}_z(y^{(\beta^*)}).$$
--
--   Together with Claim 3.21 this bounds the excess term of (19) in the proof of Lemma 3.1.
--
--   Differences from the source:
--   - generalization: x = x^{(β*)}, 'the optimal feasible assignment to y^{(β*)}', and ỹ the output of MP_β on (P, dist̃) → any x with x ∼ y^{(β*)} and σ_z(x) = cost_z(y^{(β*)}), and any ỹ ≥ 0; reason: the paper's x^{(β*)} is such an x and its ỹ is nonnegative; the claim's proof uses nothing else about them
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, definition of F and Claim 3.20, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_RobustFracMP_assignCost
import Definitions.Def_RobustFracMP_Feasible
import Definitions.Def_RobustFracMP_fracCost
import Definitions.Def_RobustFracMP_mpOutput

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.20 (far pairs).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, p.25 (PDF p.27): with `β* := 2^{−z−1}`, `x^{(β*)} ∼ y^{(β*)}` "the optimal
feasible assignment to y^{(β*)}", and the far pairs
"F := {(p, q) ∈ P × P : β* · dist^z(p, q) > 1/(3·2^{z−1}) · r^{(β*)}_p}",
"Claim 3.20. Σ_{(p,q)∈F} [x^{(β*)}_{p,q} − ỹ_q]_+ · r^{(β*)}_p ≤ 3/4 · cost_z(y^{(β*)})."

**Formalization Note.** `x` is any feasible assignment for `y^{(β*)}` whose assignment cost equals
`cost_z(y^{(β*)})` (an optimal one), and `yt` (ỹ) is any nonnegative vector; in the paper ỹ is the
output of MP_β on the distorted distance, which is nonnegative, and the claim uses nothing else
about it. `[a]_+` is `max a 0`; the sum over `F` is the sum over `p` and over `q` in the filter.
Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_20 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (x : P → P → ℝ)
    (hx : Feasible x (mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam))
    (hopt : assignCost z x = fracCost z (mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam))
    (yt : P → ℝ) (hyt : ∀ q, 0 ≤ yt q) :
    ∑ p, ∑ q ∈ Finset.univ.filter (fun q =>
        1 / (3 * 2 ^ (z - 1)) * mpRadius z dist (1 / 2 ^ (z + 1)) lam p <
          1 / 2 ^ (z + 1) * dist p q ^ z),
      max (x p q - yt q) 0 * mpRadius z dist (1 / 2 ^ (z + 1)) lam p ≤
    3 / 4 * fracCost z (mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam) := by sorry

end RobustFracMP
