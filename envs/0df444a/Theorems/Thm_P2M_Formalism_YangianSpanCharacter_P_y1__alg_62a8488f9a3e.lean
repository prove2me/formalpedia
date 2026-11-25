-- Prove2me | Theorems.Thm_P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e
-- name    : P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:59.418552+00:00
-- url     : https://prove2.me/theorems/2087b847-5ff5-4d72-80ad-6368dcdb1277
-- title:
--   P2 M Formalism Yangian Span Character P y1  alg 62a8488f9a3e: P2 M Formalism Yangian Span Character P y1  alg 62a8488f9a3e
-- statement:
--   The P2 M Formalism Yangian Span Character P y1  alg 62a8488f9a3e construction uses the P2 M Formalism Yangian Span Character P y1  alg 62a8488f9a3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L56-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/YangianRTTProofs/DiagonalEntryEqOfModularRelation.lean#L56-L75

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

theorem P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e {a b ai bi X Y : A} {c : 𝕜} (hc : c ≠ 0)
    (hR1 : c • (a * Y - Y * a) = X * b - Y * a) (hR2 : (-c) • (b * X - X * b) = Y * a - X * b)
    (hb1 : b * bi = 1) (hb2 : bi * b = 1) (ha1 : a * ai = 1) (hab : a * b = b * a) :
    a * (bi * Y) - bi * Y * a = a * (c⁻¹ • (ai * X - bi * Y)) := by sorry

alias «Formalism».«YangianSpanCharacter».«P».«y1'_alg» := P2M_Formalism_YangianSpanCharacter_P_y1__alg_62a8488f9a3e
