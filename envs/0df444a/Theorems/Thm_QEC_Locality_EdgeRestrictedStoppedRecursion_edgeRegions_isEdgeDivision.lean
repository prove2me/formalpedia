-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegions_isEdgeDivision
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegions_isEdgeDivision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:41.183626+00:00
-- url     : https://prove2.me/theorems/1ef6d557-9ba0-4db8-be6e-7beb99d676a5
-- title:
--   Edge Restricted Stopped Recursion: edge Regions is Edge Division
-- statement:
--   The stopped recursion constructs an edge division whenever its root owns all graph edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L655-L673
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L655-L673

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegions_isEdgeDivision
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hroot : edges = directedEdgeFinset G) :
    IsEdgeDivision G tree.edgeRegion tree.edgeActive := by sorry
