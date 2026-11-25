-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:28.113884+00:00
-- url     : https://prove2.me/theorems/72dab369-e842-471d-aa9f-be98c9740b7a
-- title:
--   P2 M Positivity Theory Rg Sw LVs STD trace mul single  8682ea6fcbf3: P2 M Positivity Theory Rg Sw LVs STD trace mul single  8682ea6fcbf3
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs STD trace mul single  8682ea6fcbf3 construction uses the P2 M Positivity Theory Rg Sw LVs STD trace mul single  8682ea6fcbf3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L29-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3 (β : Matrix (Fin n) (Fin n) ℂ) (r c : Fin n) :
    (β * Matrix.single r c 1).trace = β c r := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«STD».«trace_mul_single'» := P2M_PositivityTheory_Rg_Sw_LVs_STD_trace_mul_single__8682ea6fcbf3
