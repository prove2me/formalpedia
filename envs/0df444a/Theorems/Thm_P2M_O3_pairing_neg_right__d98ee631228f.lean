-- Prove2me | Theorems.Thm_P2M_O3_pairing_neg_right__d98ee631228f
-- name    : P2M_O3_pairing_neg_right__d98ee631228f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:24.170795+00:00
-- url     : https://prove2.me/theorems/565e93f7-edd4-4fe3-a8da-67ac09b07732
-- title:
--   P2 M O3 pairing neg right  d98ee631228f: P2 M O3 pairing neg right  d98ee631228f
-- statement:
--   The P2 M O3 pairing neg right  d98ee631228f construction uses the P2 M O3 pairing neg right  d98ee631228f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L40-L42
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L40-L42

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem P2M_O3_pairing_neg_right__d98ee631228f {d : ℕ} (x y : Vec d) :
    pairing x (-y) = -pairing x y := by sorry

alias «O3».«pairing_neg_right'» := P2M_O3_pairing_neg_right__d98ee631228f
