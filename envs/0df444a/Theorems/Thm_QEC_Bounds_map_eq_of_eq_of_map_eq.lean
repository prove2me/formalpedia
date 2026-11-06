-- Prove2me | Theorems.Thm_QEC_Bounds_map_eq_of_eq_of_map_eq
-- name    : QEC.Bounds.map_eq_of_eq_of_map_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:02:28.648227+00:00
-- url     : https://prove2.me/theorems/9d91c203-6246-4773-85f7-7078eebbbcd4
-- title:
--   Bounds: map eq of eq of map eq
-- statement:
--   Map an input equality once, then compose it with an equality at the mapped value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutEquality.lean#L9-L11
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutEquality.lean#L9-L11

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_BlockData
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutEquality
set_option autoImplicit false
open QEC
open QEC.Bounds

theorem QEC.Bounds.map_eq_of_eq_of_map_eq {α β : Type*} (f : α → β) {x y : α} {z : β}
    (hxy : x = y) (hyz : f y = z) : f x = z := by sorry
