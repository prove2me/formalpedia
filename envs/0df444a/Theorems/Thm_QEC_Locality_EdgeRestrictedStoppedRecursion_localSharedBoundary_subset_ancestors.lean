-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_localSharedBoundary_subset_ancestors
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.localSharedBoundary_subset_ancestors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:26.71221+00:00
-- url     : https://prove2.me/theorems/db5b87b8-f8db-41ab-9c7a-e66fdedf4dfa
-- title:
--   Edge Restricted Stopped Recursion: local Shared Boundary subset ancestors
-- statement:
--   Any shared vertex incident to a terminal region occurs in a separator on that
--   owner's ancestor route.  This removes the global edge-division definition from
--   the later quantitative boundary charge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L487-L607
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L487-L607

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.localSharedBoundary_subset_ancestors
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) :
    (edgeIncidentVertices (tree.edgeRegion owner)) ∩
      edgeDivisionSharedBoundary tree.edgeRegion tree.edgeActive ⊆
        tree.edgeOwnerAncestors owner := by sorry
