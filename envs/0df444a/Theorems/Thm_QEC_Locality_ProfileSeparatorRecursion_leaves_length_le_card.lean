-- Prove2me | Theorems.Thm_QEC_Locality_ProfileSeparatorRecursion_leaves_length_le_card
-- name    : QEC.Locality.ProfileSeparatorRecursion_leaves_length_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:29:53.647028+00:00
-- url     : https://prove2.me/theorems/7678da8f-9768-4240-bc86-44d956ba0f41
-- title:
--   Locality: Profile Separator Recursion leaves length le card
-- statement:
--   The number of nonempty leaves is bounded by the root cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L228-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L228-L253

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.ProfileSeparatorRecursion_leaves_length_le_card
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.leaves.length ≤ tree.root.card := by sorry
