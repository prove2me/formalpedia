-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_spanBundle_sub_9cccd024bf35
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_spanBundle_sub_9cccd024bf35
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:17:30.199826+00:00
-- url     : https://prove2.me/theorems/cf3ca6cb-eac5-4041-ae6c-e9beefe888a1
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Sections span Bundle sub 9cccd024bf35: P2 M Ground Theory Heights  Heights Kleiman Snapper Sections span Bundle sub 9cccd024bf35
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Sections span Bundle sub 9cccd024bf35 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Sections span Bundle sub 9cccd024bf35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperSection.lean#L60-L61

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_spanBundle_sub_9cccd024bf35 (s : Ω) (hs : s ≠ 0) (I : Chart x) :
    (spanBundle k x s hs).sub I = Submodule.span (chartRing k x I) {s} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperSections».«spanBundle_sub» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSections_spanBundle_sub_9cccd024bf35
