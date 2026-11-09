-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_1_sandwich
-- name    : RobustFracMP.lemma_3_1_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:01:28.340846+00:00
-- url     : https://prove2.me/theorems/f729ac25-beae-4e01-bc34-0b903bf3fe59
-- title:
--   Proof of Lemma 3.1 — sandwich $r^{(\beta)}\le\tilde r\le r^{(\beta^*)}$
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   Let $\varepsilon\in(0,1)$, $\beta^*=2^{-z-1}$ and $\beta=\beta^*\varepsilon^{2z}$, and let $\widetilde{\mathrm{dist}}:P\times P\to\mathbb R$ be any function with
--
--   $$\mathrm{dist}(p,q)\le\widetilde{\mathrm{dist}}(p,q)\le\varepsilon^{-2}\,\mathrm{dist}(p,q)\qquad\text{for all }p,q\in P.\qquad(9)$$
--
--   Let $\tilde r$ and $\tilde y=\tilde r/\lambda$ be computed by Algorithm 1 with scale factor $\beta$ on $(P,\widetilde{\mathrm{dist}})$. Then, entrywise,
--
--   $$r^{(\beta)}\le\tilde r\le r^{(\beta^*)}\qquad\text{and}\qquad y^{(\beta)}\le\tilde y\le y^{(\beta^*)},$$
--
--   where $r^{(\beta)},r^{(\beta^*)}$ and $y^{(\beta)},y^{(\beta^*)}$ are computed on the true metric. The distorted run is squeezed between two undistorted runs, which is how Lemma 3.12 and Lemma 3.9 transfer to the distorted output.
--
--   **Formalization Note** $\widetilde{\mathrm{dist}}$ is not assumed symmetric or a metric.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, first step, pp.24–25 (PDF pp.26–27)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_mpOutput

set_option autoImplicit false

namespace RobustFracMP

/-- **Proof of Lemma 3.1, sandwich step: r^{(β)} ≤ r̃ ≤ r^{(β*)} and y^{(β)} ≤ ỹ ≤ y^{(β*)}.**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), proof of Lemma 3.1, pp.24–25 (PDF pp.26–27): with `β* := 2^{−z−1}`, `β = β* ε^{2z}`, and `r̃`
computed by MP_β on the distorted `(P, \tilde{dist})` satisfying (9), "We first show that the vector
r̃ satisfies r^{(β)} ≤ r̃ ≤ r^{(β*)}. […] Since ỹ = r̃/λ, we have y^{(β)} ≤ ỹ ≤ y^{(β*)}."

**Formalization Note.** `distT` is `\tilde{dist}`, an arbitrary function `P → P → ℝ` satisfying (9)
`dist(p, q) ≤ \tilde{dist}(p, q) ≤ ε^{−2} dist(p, q)`; it is not assumed symmetric or a metric. All
inequalities are entrywise. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_1_sandwich {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (distT : P → P → ℝ)
    (h9 : ∀ p q, dist p q ≤ distT p q ∧ distT p q ≤ (ε ^ 2)⁻¹ * dist p q) :
    (∀ p : P,
      mpRadius z dist (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ≤
          mpRadius z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ∧
        mpRadius z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ≤
          mpRadius z dist (1 / 2 ^ (z + 1)) lam p) ∧
    ∀ p : P,
      mpOutput (P := P) z dist (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ≤
          mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ∧
        mpOutput z distT (1 / 2 ^ (z + 1) * ε ^ (2 * z)) lam p ≤
          mpOutput (P := P) z dist (1 / 2 ^ (z + 1)) lam p := by sorry

end RobustFracMP
