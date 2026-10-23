-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_positiveFourierInsufficient
-- name    : QAlgorithms.Papers.Independent.Information100.P39.positiveFourierInsufficient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:21:53.997972+00:00
-- url     : https://prove2.me/theorems/557d6bc2-e28f-44da-9ce1-70d76681a05b
-- title:
--   Appendix A.1: positive Fourier coefficients are insufficient
-- statement:
--   Apply the normalized inverse symplectic Walsh transform to the coefficient vector $(1,161/200,9/10,9/10)$ in the order $(I,X,Y,Z)$. The resulting law is
--
--   $$\nu=\tfrac1{800}(721,1,39,39).$$
--
--   It is nonnegative and normalized, and its forward transform is the specified vector, so every Fourier coefficient is strictly positive. Nevertheless $\nu$ has no independent-event representation. This gives an explicit obstruction to replacing the exact factorization criterion by Fourier positivity.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 8, Appendix A.1: positive Fourier coefficients are insufficient

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Appendix A.1, PDF p.8: strictly positive Fourier coefficients do not imply
independent events; all displayed decimals are encoded as exact rationals. -/
theorem positiveFourierInsufficient :
    Learning.IsDistribution positiveFourierLaw ∧
    positiveFourierLaw = pauliVector (![721/800,1/800,39/800,39/800]) ∧
    SparsePauliNoise.eigenvalueWHT positiveFourierLaw =
      pauliVector (![1,161/200,9/10,9/10]) ∧
    (∀ u, 0 < SparsePauliNoise.eigenvalueWHT positiveFourierLaw u) ∧
    ¬ HasIndependentEvents positiveFourierLaw := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
