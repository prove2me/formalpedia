-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_finiteChainRule
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_finiteChainRule
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:05:03.087651+00:00
-- url     : https://prove2.me/theorems/85760e4d-5ece-4855-aadd-088e973448f8
-- title:
--   Finite-dimensional conditional entropy chain identity
-- statement:
--   Let rho_ABCD be any normalized state on finite-dimensional complex quantum systems A, B, C and D. All conditional entropies below use marginals of this state and natural logarithms. Then
--   $$H(AB|CD)=H(A|CD)+H(B|CD)-\bigl(H(A|CD)-H(A|BCD)\bigr).$$
--
--   This is the finite-dimensional chain identity used to obtain common-conditioning subadditivity. Every term is finite; the repeated H(A|CD) is intentional.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 6, §2, finite-dimensional chain-rule identity (11)

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

/-- Finite-dimensional chain-rule identity (11), PDF p.6, with the repeated
H(A|CD) exactly as printed. No entropy identity is assumed as a premise. -/
theorem conditionalEntropy_finiteChainRule {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (rho : State ((A × B) × (C × D))) :
    finiteFirstConditionalEntropy rho.coefficients =
      finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)) +
        finiteFirstConditionalEntropy (traceFirst (associateRight rho.coefficients)) -
          (finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)) -
            finiteFirstConditionalEntropy (associateRight rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
