-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:59.379445+00:00
-- url     : https://prove2.me/theorems/6e54485b-c4f3-5ebd-966f-3bddba840eda
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop pow add le abec59476fd6: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop pow add le abec59476fd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop pow add le abec59476fd6 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop pow add le abec59476fd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L16-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop
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
open Filter
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6 (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    ∀ e : ℕ, (n + c) ^ e ≤ n ^ e + ((1 + c) ^ e - 1) * (n ^ e / n)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«pow_add_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_pow_add_le_abec59476fd6
