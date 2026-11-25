-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:36:03.577133+00:00
-- url     : https://prove2.me/theorems/6210d038-eac4-5166-812b-7caefe7dcf5c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real X 300581b331cd: P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real X 300581b331cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real X 300581b331cd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Two Cases Derivatives sum Pderiv Real X 300581b331cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/SumPderivRealApply.lean#L32-L40

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (σ : Fin f) (i : Fin (j + k)) :
    sumPderivReal f j k τ s g (X (σ, i)) =
      ∑ l ∈ s, if σ = τ ∧ i = g l then (1 : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«TwoCasesDerivatives».«sumPderivReal_X» := P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd
