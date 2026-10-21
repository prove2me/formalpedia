-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_standardFormula
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_standardFormula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:01:03.628865+00:00
-- url     : https://prove2.me/theorems/be8103d6-9163-43a6-b1af-6382dacbcb9e
-- title:
--   Agreement with the standard conditional entropy
-- statement:
--   Let rho_AC be a normalized trace-class state on separable complex systems A and C. Suppose H(C)<infinity and H(A)<infinity. With conditional entropy defined by H(C|A)=H(C)-D(rho_AC || rho_A tensor rho_C), using natural logarithms,
--   $$H(C|A)=H(AC)-H(A).$$
--
--   This identifies the extended definition with the usual entropy difference on its finite-marginal domain. Joint entropy finiteness follows from the hypotheses.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, unnumbered result after (2): recovery of the standard entropy difference

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

/-- Agreement with the standard entropy difference after (2), PDF p.2.
The preceding H(C)<infinity assumption and the additional H(A)<infinity are retained. -/
theorem conditionalEntropy_standardFormula {A C : Type} [Countable A] [Countable C]
    (rho : State (A × C))
    (hC : homogeneousEntropy (traceFirst rho.coefficients) < ⊤)
    (hA : homogeneousEntropy (traceSecond rho.coefficients) < ⊤) :
    finiteFirstConditionalEntropy (swapCoeff rho.coefficients) =
      (homogeneousEntropy rho.coefficients : EReal) -
        (homogeneousEntropy (traceSecond rho.coefficients) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
