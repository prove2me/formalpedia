-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_existsUnique_edgeOwner
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.existsUnique_edgeOwner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:52.743797+00:00
-- url     : https://prove2.me/theorems/09ce7848-34cd-4d84-bdb3-582aed412219
-- title:
--   Edge Restricted Stopped Recursion: exists Unique edge Owner
-- statement:
--   Every edge in the current edge set has a unique terminal owner.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L610-L652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L610-L652

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.existsUnique_edgeOwner
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.edgeOwnerType, edge ∈ tree.edgeRegion owner := by sorry
