-- Prove2me | Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc
-- name    : P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:46.252548+00:00
-- url     : https://prove2.me/theorems/05fcf44e-64fd-44e7-ac25-c0627f6a4f88
-- title:
--   P2 M Formalism Yangian Span Character P y1  mod 9fb34041d8dc: P2 M Formalism Yangian Span Character P y1  mod 9fb34041d8dc
-- statement:
--   The P2 M Formalism Yangian Span Character P y1  mod 9fb34041d8dc construction uses the P2 M Formalism Yangian Span Character P y1  mod 9fb34041d8dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L154-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L154-L159

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_DiagonalEntryEqOfModularRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {t : 𝕜 → Matrix (Fin 2) (Fin 2) A}
  {τinv : 𝕜 → A} {q : 𝕜 → 𝕜} {S : Set 𝕜}

theorem P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc (H : ModHyp t τinv q S) {u v : 𝕜} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    t u 1 1 * mf t τinv v - mf t τinv v * t u 1 1 = t u 1 1 * mu t τinv u v := by sorry

alias «Formalism».«YangianSpanCharacter».«P».«y1'_mod» := P2M_Formalism_YangianSpanCharacter_P_y1__mod_9fb34041d8dc
