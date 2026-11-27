-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_3dbdee3c0213
-- name    : P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_3dbdee3c0213
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:25.845131+00:00
-- url     : https://prove2.me/theorems/fb0e0757-b2bb-4e6a-aa7a-f904d85aef29
-- title:
--   P2 M Ground Theory Global automorphism Order of a  eq zero 3dbdee3c0213: P2 M Ground Theory Global automorphism Order of a  eq zero 3dbdee3c0213
-- statement:
--   The P2 M Ground Theory Global automorphism Order of a  eq zero 3dbdee3c0213 construction uses the P2 M Ground Theory Global automorphism Order of a  eq zero 3dbdee3c0213 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/WeberFunctionAutomorphisms.lean#L19-L21

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

theorem P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_3dbdee3c0213 {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0) :
    automorphismOrder W = 6 := by sorry

alias «GroundTheory».«Global».«automorphismOrder_of_a₄_eq_zero» := P2M_GroundTheory_Global_automorphismOrder_of_a__eq_zero_3dbdee3c0213
