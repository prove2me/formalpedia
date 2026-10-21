-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_commonConditioning
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_commonConditioning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:05:38.872353+00:00
-- url     : https://prove2.me/theorems/feb9536f-f82e-463b-8cd1-ad8862d23caf
-- title:
--   Subadditivity with a common conditioning system
-- statement:
--   Let rho_ABCD be a normalized trace-class state on arbitrary separable complex systems, with H(A)<infinity and H(B)<infinity. Then
--   $$H(AB|CD)\le H(A|CD)+H(B|CD).$$
--
--   The conditioning system CD may be infinite-dimensional and may have infinite entropy. Finite H(AB) follows from the two marginal assumptions, so all conditional entropies are in their defining domains.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 6, §2, conditional subadditivity with a common conditioning register (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Common-conditioning subadditivity (12), PDF pp.6–7, including infinite CD.
Finite H(AB) follows from finite H(A) and H(B); it is not an extra premise. -/
theorem conditionalEntropy_commonConditioning {A B C D : Type}
    [Countable A] [Countable B] [Countable C] [Countable D]
    (rho : State ((A × B) × (C × D)))
    (hA : homogeneousEntropy (traceSecond (traceSecond rho.coefficients)) < ⊤)
    (hB : homogeneousEntropy (traceFirst (traceSecond rho.coefficients)) < ⊤) :
    finiteFirstConditionalEntropy rho.coefficients ≤
      finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)) +
        finiteFirstConditionalEntropy (traceFirst (associateRight rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
