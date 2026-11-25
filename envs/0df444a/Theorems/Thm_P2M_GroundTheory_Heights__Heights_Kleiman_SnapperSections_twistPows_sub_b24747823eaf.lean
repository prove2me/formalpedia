-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_twistPows_sub_b24747823eaf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_twistPows_sub_b24747823eaf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:25.295614+00:00
-- url     : https://prove2.me/theorems/ea5f5b51-7b9d-4722-b2bf-7fc44130d103
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections twist Pows sub b24747823eaf: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections twist Pows sub b24747823eaf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections twist Pows sub b24747823eaf construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections twist Pows sub b24747823eaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L29-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_MulQuotEqSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionNonvanishSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutZeroNotLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AssemblyBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSections
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_twistPows_sub_b24747823eaf (F : SubSystem k x Ω) : ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ)
    (I : Chart x), (F.twistPows t L n).sub I = F.sub I * ∏ j, (L j).sub I ^ n j
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«twistPows_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_twistPows_sub_b24747823eaf
