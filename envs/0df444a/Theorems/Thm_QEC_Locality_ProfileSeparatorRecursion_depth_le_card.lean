-- Prove2me | Theorems.Thm_QEC_Locality_ProfileSeparatorRecursion_depth_le_card
-- name    : QEC.Locality.ProfileSeparatorRecursion_depth_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:30:32.560199+00:00
-- url     : https://prove2.me/theorems/83317082-bd24-44fd-a84a-fa7459a6ae7f
-- title:
--   Locality: Profile Separator Recursion depth le card
-- statement:
--   Strict child descent bounds recursion depth by the root cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L256-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Recursion.lean#L256-L268

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.ProfileSeparatorRecursion_depth_le_card
    {G : ConnectivityGraph ι} {r : Nat} {vertices : Finset ι}
    (tree : ProfileSeparatorRecursion G r vertices) :
    tree.depth ≤ tree.root.card := by sorry
