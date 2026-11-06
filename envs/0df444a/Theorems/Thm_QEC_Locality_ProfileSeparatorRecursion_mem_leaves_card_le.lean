-- Prove2me | Theorems.Thm_QEC_Locality_ProfileSeparatorRecursion_mem_leaves_card_le
-- name    : QEC.Locality.ProfileSeparatorRecursion.mem_leaves_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:29:30.284479+00:00
-- url     : https://prove2.me/theorems/19ee1a5f-f32e-445c-8682-320764729151
-- title:
--   Profile Separator Recursion: mem leaves card le
-- statement:
--   Every recursively produced leaf obeys the requested cardinality cap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L189-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L189-L201

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.ProfileSeparatorRecursion.mem_leaves_card_le
    {G : ConnectivityGraph ι} {r : Nat} {vertices leaf : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) (hleaf : leaf ∈ tree.leaves) :
    leaf.card ≤ r := by sorry
