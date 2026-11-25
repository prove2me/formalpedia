-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:29:58.508822+00:00
-- url     : https://prove2.me/theorems/ce01a2ef-3ce1-457e-b48e-4377d21affb3
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists common multiple 06ca60e23aba: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists common multiple 06
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists common multiple 06ca60e23aba construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form exists common multiple 06ca60e23aba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L52-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
variable {E : Type*} [Field E] [NumberField E]
omit [Field E] [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (hP : ∀ i a b, P i a → a ∣ b → P i b) (hex : ∀ i ∈ s, ∃ a, 0 < a ∧ P i a) :
    ∃ d, 0 < d ∧ ∀ i ∈ s, P i d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«exists_common_multiple» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_exists_common_multiple_06ca60e23aba
