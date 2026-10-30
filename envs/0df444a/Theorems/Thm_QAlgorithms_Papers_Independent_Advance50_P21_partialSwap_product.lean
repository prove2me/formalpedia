-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_partialSwap_product
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.partialSwap_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:52:58.26138+00:00
-- url     : https://prove2.me/theorems/f8b5d536-ba6e-47f2-8e81-fad497912e65
-- title:
--   Lemma 9: output of a partial swap channel on product states
-- statement:
--   Let $d\ge1$, let $\rho,\sigma$ be positive semidefinite complex $d\times d$ matrices of trace one, and let $a\in[0,1]$. Write
--   $$
--   \rho\boxplus_a\sigma=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}(\rho\sigma-\sigma\rho).
--   $$
--
--   Let $S|i,j\rangle=|j,i\rangle$, $U_a=\sqrt a\,I+i\sqrt{1-a}\,S$, and $\mathcal E_a(X)=\operatorname{Tr}_2(U_aXU_a^\dagger)$. Then
--   $$\mathcal E_a(\rho\otimes\sigma)=a\rho+(1-a)\sigma-i\sqrt{a(1-a)}[\rho,\sigma],$$
--   where $[\rho,\sigma]=\rho\sigma-\sigma\rho$. This identifies the product-input action of the constructed channel; at $a=1$ it returns $\rho$, and at $a=0$ it returns $\sigma$.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 10, Lemma 9: output of a partial swap channel on product states

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.10, Lemma 9, (4.10): product-input channel output, with the source's minus i sign. -/
theorem partialSwap_product {d : ℕ} (hd : 0 < d) (rho sigma : Mat d)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    partialSwapChannel d a (Matrix.kronecker rho sigma) =
      a • rho + (1 - a) • sigma -
        ((Real.sqrt (a * (1 - a)) : ℂ) * Complex.I) • (rho * sigma - sigma * rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
