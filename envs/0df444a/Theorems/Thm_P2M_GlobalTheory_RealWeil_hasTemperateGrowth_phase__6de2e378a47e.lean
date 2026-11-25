-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RealWeil_hasTemperateGrowth_phase__6de2e378a47e
-- name    : P2M_GlobalTheory_RealWeil_hasTemperateGrowth_phase__6de2e378a47e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:19.376705+00:00
-- url     : https://prove2.me/theorems/764cd87b-248b-4cb1-b507-c50c2c81aa93
-- title:
--   P2 M Global Theory Real Weil has Temperate Growth phase  6de2e378a47e: P2 M Global Theory Real Weil has Temperate Growth phase  6de2e378a47e
-- statement:
--   The P2 M Global Theory Real Weil has Temperate Growth phase  6de2e378a47e construction uses the P2 M Global Theory Real Weil has Temperate Growth phase  6de2e378a47e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzTranslate.lean#L21-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]

theorem P2M_GlobalTheory_RealWeil_hasTemperateGrowth_phase__6de2e378a47e (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by sorry

alias «GlobalTheory».«RealWeil».«hasTemperateGrowth_phase'» := P2M_GlobalTheory_RealWeil_hasTemperateGrowth_phase__6de2e378a47e
