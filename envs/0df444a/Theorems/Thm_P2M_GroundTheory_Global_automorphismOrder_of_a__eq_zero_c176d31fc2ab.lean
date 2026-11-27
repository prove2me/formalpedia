-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_c176d31fc2ab
-- name    : P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_c176d31fc2ab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:13:12.723088+00:00
-- url     : https://prove2.me/theorems/c16f5c4e-a8e7-5833-afd1-3bfda48e758f
-- title:
--   P2 M Ground Theory Global automorphism Order of a  eq zero c176d31fc2ab: P2 M Ground Theory Global automorphism Order of a  eq zero c176d31fc2ab
-- statement:
--   The P2 M Ground Theory Global automorphism Order of a  eq zero c176d31fc2ab construction uses the P2 M Ground Theory Global automorphism Order of a  eq zero c176d31fc2ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]

theorem P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_c176d31fc2ab {W : WeierstrassCurve F} (hb : W.a₆ = 0) : automorphismOrder W = 4 := by sorry

alias «GroundTheory».«Global».«automorphismOrder_of_a₆_eq_zero» := P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_c176d31fc2ab
