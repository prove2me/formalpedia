-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:40.206382+00:00
-- url     : https://prove2.me/theorems/ec1c6d9f-678e-4a43-bc4f-c484ceeb5f16
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real apply fbdf56144058: P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real apply fbdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real apply fbdf56144058 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real apply fbdf56144058 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L22-L30

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058 {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    sumPderivReal f j k τ s g P = ∑ l ∈ s, pderiv (τ, g l) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TwoCasesDerivatives».«sumPderivReal_apply» := P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
