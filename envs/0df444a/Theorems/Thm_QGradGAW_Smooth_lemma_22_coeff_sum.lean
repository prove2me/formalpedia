-- Prove2me | Theorems.Thm_QGradGAW_Smooth_lemma_22_coeff_sum
-- name    : QGradGAW.Smooth.lemma_22_coeff_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:24.451165+00:00
-- url     : https://prove2.me/theorems/cd19720a-5abf-4244-9d8e-0fdf1f069198
-- title:
--   Lemma 22, (24), p. 28 — Σ_{ℓ=0}^{m} |a_ℓ^(2m)| < Σ_{ℓ=1}^{m} 1/ℓ ≤ ln(m) + 1
-- statement:
--   For every integer $m\ge1$ the central difference coefficients of Definition 7 satisfy
--   $$\sum_{\ell=0}^{m}\big|a_\ell^{(2m)}\big|\;<\;\sum_{\ell=1}^{m}\frac1\ell\;\le\;\ln(m)+1 .$$
--
--   Since $|a_{-\ell}^{(2m)}|=|a_\ell^{(2m)}|$, the total $\sum_{\ell=-m}^m|a_\ell^{(2m)}|$ is at most $2\ln(m)+2$; this bounds the number of fractional queries of one central-difference oracle call (display (25)).
--
--   **Formalization Note** $m\ge1$ because the paper's $\mathbb N$ starts at $1$ (for $m=0$ both sums are empty and the strict inequality fails).
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, p. 28, Lemma 22, display (24)

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

namespace QGradGAW.Smooth

/-- arXiv:1711.00465v3, p. 28, Lemma 22, display (24): for `m ∈ ℕ₊`,
`Σ_{ℓ=0}^{m} |a_ℓ^(2m)| < Σ_{ℓ=1}^{m} 1/ℓ ≤ ln(m) + 1`. -/
theorem lemma_22_coeff_sum (m : ℕ) (hm : 1 ≤ m) :
    ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| < ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ∧
      ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ≤ Real.log m + 1 := by sorry

end QGradGAW.Smooth
