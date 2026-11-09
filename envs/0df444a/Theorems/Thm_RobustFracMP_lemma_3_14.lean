-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_14
-- name    : RobustFracMP.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:00:43.22679+00:00
-- url     : https://prove2.me/theorems/e72681ba-11a4-4714-800f-d8e209716ce6
-- title:
--   Lemma 3.14 — LMP inequality for the assignment cost of $x^{(\beta)}$
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\beta^*=2^{-z-1}$ and $0<\beta\le\beta^*$, let $y^{(\beta)}=r^{(\beta)}/\lambda$ be the output of Algorithm 1 on $(P,\mathrm{dist})$, and let $x^{(\beta)}$ be the assignment (15). Then
--
--   $$\sigma_z(x^{(\beta)})\le\beta^{-1}\bigl(\widehat{\mathrm{OPT}}^{\mathrm{fl}}_z(\lambda)-\lambda\|y^{(\beta)}\|_1\bigr).$$
--
--   This is the primal-dual half of Lemma 3.12: the vector $r^{(2\beta)}$ is a feasible dual solution of the facility-location LP.
--
--   Differences from the source:
--   - reading: stated inside the proof of Lemma 3.12, whose statement fixes β ∈ (0, β*], β* = 2^{−z−1} (p.19) → hypotheses 0 < β and β ≤ 1 / 2 ^ (z + 1); reason: the claim's own sentence names no range for β; its context does
--   - encoding: ‖y‖₁ for y ≥ 0 → ∑ p, y p; reason: the entries are nonnegative, so the sum is the ℓ₁ norm
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.14, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_RobustFracMP_assignCost
import Definitions.Def_RobustFracMP_optFL
import Definitions.Def_RobustFracMP_mpOutput
import Definitions.Def_RobustFracMP_xBeta

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.14 (the assignment x^{(β)} satisfies the LMP inequality).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.14, p.21 (PDF p.23): "σ_z(x^{(β)}) ≤ β^{−1} · (\widehat{OPT}^{fl}_z(λ) − λ · ‖y^{(β)}‖₁)."

Here `x^{(β)}` is (15) (`xBeta`), `y^{(β)} = r^{(β)}/λ` is the output of MP_β on `(P, dist)`, and the
lemma sits inside the proof of Lemma 3.12, which fixes `β ∈ (0, β*]`, `β* = 2^{−z−1}` (p.19).

**Formalization Note.** `‖y^{(β)}‖₁` is `∑ p, y^{(β)}_p` (the entries are nonnegative). Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_14 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β)
    (hβs : β ≤ 1 / 2 ^ (z + 1)) :
    assignCost z (xBeta (P := P) z β lam) ≤
      β⁻¹ * (optFL P z lam - lam * ∑ p, mpOutput (P := P) z dist β lam p) := by sorry

end RobustFracMP
