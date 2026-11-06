-- Prove2me | Theorems.Thm_QEC_Locality_ProfileSeparatorRecursion_separatorUnion_union_leafUnion
-- name    : QEC.Locality.ProfileSeparatorRecursion.separatorUnion_union_leafUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:29:52.225376+00:00
-- url     : https://prove2.me/theorems/c6c2e223-4a0e-48f9-831c-6aea44c398c4
-- title:
--   Profile Separator Recursion: separator Union union leaf Union
-- statement:
--   Removed separators together with the leaf union cover the root exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L204-L225
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L204-L225

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.ProfileSeparatorRecursion.separatorUnion_union_leafUnion
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.separatorUnion ∪ tree.leafUnion = tree.root := by sorry
