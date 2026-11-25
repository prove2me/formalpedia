-- Prove2me | Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4
-- name    : P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:03.831307+00:00
-- url     : https://prove2.me/theorems/d8db31e8-a1ae-4098-978f-411a4f0b3320
-- title:
--   P2 M Formalism Yangian Span Character P from comm  4b04a0b711b4: P2 M Formalism Yangian Span Character P from comm  4b04a0b711b4
-- statement:
--   The P2 M Formalism Yangian Span Character P from comm  4b04a0b711b4 construction uses the P2 M Formalism Yangian Span Character P from comm  4b04a0b711b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L33-L37

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
variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4 {b m e : A} (h : b * m - m * b = b * e) : m * b = b * (m - e) := by sorry

alias «Formalism».«YangianSpanCharacter».«P».«from_comm'» := P2M_Formalism_YangianSpanCharacter_P_from_comm__4b04a0b711b4
