-- Prove2me | Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
-- name    : QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:12:43.716291+00:00
-- url     : https://prove2.me/theorems/5d298b94-62da-4812-8d34-fb1b3d5ab8ca
-- title:
--   Edge Restricted Stopped Recursion: edge Region subset
-- statement:
--   Every terminal region is a subset of its recursion-node edge set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L351-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L351-L364

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.EdgeRestrictedStoppedRecursion.edgeRegion_subset
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (owner : tree.edgeOwnerType) : tree.edgeRegion owner ⊆ edges := by sorry
