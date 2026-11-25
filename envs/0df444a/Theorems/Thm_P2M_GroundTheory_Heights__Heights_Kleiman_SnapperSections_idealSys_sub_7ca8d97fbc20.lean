-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealSys_sub_7ca8d97fbc20
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealSys_sub_7ca8d97fbc20
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:44.721511+00:00
-- url     : https://prove2.me/theorems/2025f9be-69ee-5e5a-86be-5e02f5fae46c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Sys sub 7ca8d97fbc20: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Sys sub 7ca8d97fbc20
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Sys sub 7ca8d97fbc20 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Sys sub 7ca8d97fbc20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L56-L56

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealSys_sub_7ca8d97fbc20 (pp : Ideal (Poly k N)) (I : Chart x) : (idealSys x pp).sub I = idealMod (x := x) pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«idealSys_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealSys_sub_7ca8d97fbc20
