-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_mul_le_mul_sub_047c9fa6e5b7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_mul_le_mul_sub_047c9fa6e5b7
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:09.691628+00:00
-- url     : https://prove2.me/theorems/e7761133-effd-5e2f-a51a-1503405af740
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections mul le mul sub 047c9fa6e5b7: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections mul le mul sub 047c9fa6e5b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections mul le mul sub 047c9fa6e5b7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections mul le mul sub 047c9fa6e5b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L73-L75

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_mul_le_mul_sub_047c9fa6e5b7 {I : Chart x} {P Q P' Q' : Submodule (chartRing k x I) Ω} (h₁ : P ≤ P') (h₂ : Q ≤ Q') :
    P * Q ≤ P' * Q' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«mul_le_mul_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_mul_le_mul_sub_047c9fa6e5b7
