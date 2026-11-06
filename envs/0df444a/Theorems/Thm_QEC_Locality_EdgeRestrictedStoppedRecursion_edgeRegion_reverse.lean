-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_reverse
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:47.608392+00:00
-- url     : https://prove2.me/theorems/97d25368-b42b-44d2-8e16-1935f85dc445
-- title:
--   Edge Restricted Stopped Recursion: edge Region reverse
-- statement:
--   Every terminal region remains reverse-symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L367-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L367-L379

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_reverse
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) (x y : ι) :
    (x, y) ∈ tree.edgeRegion owner ↔ (y, x) ∈ tree.edgeRegion owner := by sorry
