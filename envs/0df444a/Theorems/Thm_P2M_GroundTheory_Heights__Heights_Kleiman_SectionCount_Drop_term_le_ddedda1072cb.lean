-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:04:01.696274+00:00
-- url     : https://prove2.me/theorems/e06f1c09-1429-560d-8bbc-ae9825f17996
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop term le ddedda1072cb: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop term le ddedda1072cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop term le ddedda1072cb construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop term le ddedda1072cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L41-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L41-L98

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb (I C c n h : ℝ) (e d : ℕ) (hed : e ≤ d) (hc : 0 ≤ c) (hn : 1 ≤ n)
    (hh : |h - I * (n + c) ^ e / (e.factorial : ℝ)| ≤ C * (n + c) ^ e / (n + c)) :
    h ≤ (if e = d then I else 0) * n ^ d / (d.factorial : ℝ) +
      (|I| + |C|) * (1 + c) ^ e * (n ^ d / n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«term_le» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_term_le_ddedda1072cb
