-- Prove2me | Theorems.Thm_StochApproxDyn_MartingaleNoise_holder_eq14
-- name    : StochApproxDyn.MartingaleNoise.holder_eq14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:47:29.445978+00:00
-- url     : https://prove2.me/theorems/a4cf3445-6258-4898-9ae7-ec59a595c694
-- title:
--   Inequality (14): $(\sum|\alpha_i\beta_i|)^u\le(\sum\alpha_i^{\delta u/(u-1)})^{u-1}\sum\alpha_i^{(1-\delta)u}|\beta_i|^u$
-- statement:
--   Let $(\alpha_i)_{i\in I}$ and $(\beta_i)_{i\in I}$ be finite families of real numbers with $\alpha_i\ge0$, and let $u>1$ and $0<\delta<1$. Then
--   $$\Big(\sum_i|\alpha_i\beta_i|\Big)^u\le\Big(\sum_i\alpha_i^{\delta u/(u-1)}\Big)^{u-1}\sum_i\alpha_i^{(1-\delta)u}|\beta_i|^u .$$
--
--   In the proof of Proposition 4.2 this inequality, applied with $u=q/2$, $\delta=(q-2)/2q$, $\alpha_i=\gamma_{i+1}^2$ and $\beta_i=\|U_{i+1}\|^2$, converts the square function of Burkholder's inequality into a weighted sum of $q$-th moments.
--
--   **Formalization Note** All powers are real powers of nonnegative numbers. The index set is an arbitrary finite set.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.2, p. 15 (PDF p. 16), inequality (14)

import Mathlib

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, inequality (14), p. 15: for any finite family
with `α_i ≥ 0`, `β_i ∈ ℝ`, and any `u > 1`, `0 < δ < 1`,
`(∑_i |α_i β_i|)^u ≤ (∑_i α_i^{δu/(u-1)})^{u-1} ∑_i α_i^{(1-δ)u} |β_i|^u`. All powers are real
powers (`Real.rpow`) of nonnegative bases. -/
theorem holder_eq14 {ι : Type*} (s : Finset ι) (α β : ι → ℝ) (hα : ∀ i ∈ s, 0 ≤ α i)
    (u δ : ℝ) (hu : 1 < u) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∑ i ∈ s, |α i * β i|) ^ u ≤
      (∑ i ∈ s, α i ^ (δ * u / (u - 1))) ^ (u - 1) *
        ∑ i ∈ s, α i ^ ((1 - δ) * u) * |β i| ^ u := by sorry

end StochApproxDyn.MartingaleNoise
