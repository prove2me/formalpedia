-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:13.48803+00:00
-- url     : https://prove2.me/theorems/63f576b1-1a11-4056-94c3-93456f74efeb
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives deriv rest Poly 55a6298dcaea: P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives deriv rest Poly 55a6298dcaea
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives deriv rest Poly 55a6298dcaea construction uses the P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives deriv rest Poly 55a6298dcaea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L42-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L42-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
open MvPolynomial Finset
noncomputable section
variable (f j k : ℕ)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea (D : Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k))
    (bot : Bool) (α β : Fin f → ℝ)
    (ht : ∀ σ (a : Fin j), D (X (σ, Fin.castAdd k a)) = C (α σ))
    (hb : ∀ σ (b : Fin k), D (X (σ, Fin.natAdd j b)) = C (β σ)) :
    D (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) =
      C (((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) *
          (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))) *
        IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TwoCasesDerivatives».«deriv_restPoly» := P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea
