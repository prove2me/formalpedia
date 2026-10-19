-- Prove2me | Theorems.Thm_QGradGAW_Smooth_lemma_34
-- name    : QGradGAW.Smooth.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:55.472559+00:00
-- url     : https://prove2.me/theorems/ed2dbce3-0f69-4d68-995d-526b78ec3a3d
-- title:
--   Lemma 34, p. 48 — Σ_ℓ |a_ℓ^(2m) ℓ^{k+1}| ≤ 6e^{−7m/6} m^{k+3/2} for m ≥ 1, k ≥ 2m
-- statement:
--   Let $a_\ell^{(2m)}$ be the central difference coefficients of Definition 7. For every integer $m\ge1$ and every integer $k\ge 2m$,
--   $$\sum_{\ell=-m}^{m}\Big|a_\ell^{(2m)}\,\ell^{k+1}\Big|\;\le\;6\,e^{-7m/6}\,m^{k+3/2}.$$
--
--   The bound controls the higher moments $\sum_\ell a_\ell^{(2m)}\ell^{k}$ that make up the truncation error of the central difference formula; it is used for Lemma 22 and Theorem 24.
--
--   **Formalization Note** $m^{k+3/2}$ is a real power of the real number $m$.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 48, Lemma 34, display (46)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 48, Lemma 34, display (46): for all `m ∈ ℕ₊` and `k ≥ 2m`,
`Σ_{ℓ=−m}^{m} |a_ℓ^(2m) ℓ^{k+1}| ≤ 6 e^{−7m/6} m^{k+3/2}`. -/
theorem lemma_34 (m k : ℕ) (hm : 1 ≤ m) (hk : 2 * m ≤ k) :
    ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, |centralCoeff m ℓ * (ℓ : ℝ) ^ (k + 1)| ≤
      6 * Real.exp (-(7 * (m : ℝ) / 6)) * (m : ℝ) ^ ((k : ℝ) + 3 / 2) := by sorry

end QGradGAW.Smooth
