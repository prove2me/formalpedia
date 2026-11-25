-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealMod_le_one_28f34d875536
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealMod_le_one_28f34d875536
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:57.542835+00:00
-- url     : https://prove2.me/theorems/f0e89a22-fc05-52ef-a9d1-2894744be88a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Mod le one 28f34d875536: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Mod le one 28f34d875536
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Mod le one 28f34d875536 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections ideal Mod le one 28f34d875536 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L77-L80

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealMod_le_one_28f34d875536 (pp : Ideal (Poly k N)) (I : Chart x) : idealMod (x := x) pp I ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«idealMod_le_one» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_idealMod_le_one_28f34d875536
