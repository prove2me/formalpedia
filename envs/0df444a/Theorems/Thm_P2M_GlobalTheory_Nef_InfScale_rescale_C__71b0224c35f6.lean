-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6
-- name    : P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:16.719107+00:00
-- url     : https://prove2.me/theorems/d213f2ca-4ae3-5ba9-959c-a04814b1d9f4
-- title:
--   P2 M Global Theory Nef Inf Scale rescale C  71b0224c35f6: P2 M Global Theory Nef Inf Scale rescale C  71b0224c35f6
-- statement:
--   The P2 M Global Theory Nef Inf Scale rescale C  71b0224c35f6 construction uses the P2 M Global Theory Nef Inf Scale rescale C  71b0224c35f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean#L113-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]

theorem P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6 (c a : F) : PowerSeries.rescale c (PowerSeries.C a) = PowerSeries.C a := by sorry

alias «GlobalTheory».«Nef».«InfScale».«rescale_C'» := P2M_GlobalTheory_Nef_InfScale_rescale_C__71b0224c35f6
