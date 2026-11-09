-- Prove2me | Theorems.Thm_RobustFracMP_claim_3_21
-- name    : RobustFracMP.claim_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:01.56284+00:00
-- url     : https://prove2.me/theorems/7948d7ca-a350-46d2-b2fc-d93c88b5fe94
-- title:
--   Claim 3.21 — close pairs
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\beta^*=2^{-z-1}$ and $y^{(\beta^*)}=r^{(\beta^*)}/\lambda$. Let $x$ be a feasible assignment for $y^{(\beta^*)}$ and let $\tilde y\in\mathbb R^P$ with $\tilde y\le y^{(\beta^*)}$ entrywise. With the close pairs
--
--   $$\mathcal C=\Bigl\{(p,q)\in P\times P:\ \beta^*\,\mathrm{dist}^z(p,q)\le\frac1{3\cdot2^{z-1}}\,r^{(\beta^*)}_p\Bigr\},$$
--
--   $$\sum_{(p,q)\in\mathcal C}[x_{p,q}-\tilde y_q]_+\cdot r^{(\beta^*)}_p\le3\cdot2^{z-1}\cdot\lambda\cdot\bigl(\|y^{(\beta^*)}\|_1-\|\tilde y\|_1\bigr).$$
--
--   The excess on close pairs is paid by the drop in total opening from $y^{(\beta^*)}$ to $\tilde y$, which is what makes the final bound of Lemma 3.1 an LMP bound.
--
--   Differences from the source:
--   - generalization: x = x^{(β*)}, the optimal feasible assignment to y^{(β*)}, and ỹ the output of MP_β on (P, dist̃) → any x with x ∼ y^{(β*)}, and any ỹ with ỹ ≤ y^{(β*)} entrywise; reason: the proof uses only (C2) for x and ỹ ≤ y^{(β*)} (the sandwich step) for ỹ; the paper's x and ỹ satisfy both
--   - encoding: ‖y‖₁ for y ≥ 0 → ∑ p, y p; reason: the entries are nonnegative, so the sum is the ℓ₁ norm
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, definition of C and Claim 3.21, pp.25–26 (PDF pp.27–28)

import Mathlib
import Definitions.Def_RobustFracMP_Feasible
import Definitions.Def_RobustFracMP_mpOutput

set_option autoImplicit false

namespace RobustFracMP

/-- **Claim 3.21 (close pairs).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, pp.25–26 (PDF pp.27–28): with `β* := 2^{−z−1}`, `x^{(β*)} ∼ y^{(β*)}`, and
the close pairs "C := {(p, q) ∈ P × P : β* · dist^z(p, q) ≤ 1/(3·2^{z−1}) · r^{(β*)}_p}",
"Claim 3.21. Σ_{(p,q)∈C} [x^{(β*)}_{p,q} − ỹ_q]_+ · r^{(β*)}_p ≤ 3 · 2^{z−1} · λ ·
(‖y^{(β*)}‖₁ − ‖ỹ‖₁)."

**Formalization Note.** `x` is any feasible assignment for `y^{(β*)}` (the proof uses only (C2),
`x ≤ y^{(β*)}`), and `yt` (ỹ) is any vector with `ỹ ≤ y^{(β*)}` entrywise (what the proof uses, from
the sandwich step). `‖·‖₁` is the plain sum (the paper's vectors are nonnegative). Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem claim_3_21 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (x : P → P → ℝ)
    (hx : Feasible x (mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam))
    (yt : P → ℝ) (hyt : ∀ q, yt q ≤ mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam q) :
    ∑ p, ∑ q ∈ Finset.univ.filter (fun q =>
        1 / 2 ^ (z + 1) * dist p q ^ z ≤
          1 / (3 * 2 ^ (z - 1)) * mpRadius z dist (1 / 2 ^ (z + 1)) lam p),
      max (x p q - yt q) 0 * mpRadius z dist (1 / 2 ^ (z + 1)) lam p ≤
    3 * 2 ^ (z - 1) * lam *
      (∑ p, mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam p - ∑ p, yt p) := by sorry

end RobustFracMP
