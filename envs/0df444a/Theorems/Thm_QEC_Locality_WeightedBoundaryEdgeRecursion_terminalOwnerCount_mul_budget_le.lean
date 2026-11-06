-- Prove2me | Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_terminalOwnerCount_mul_budget_le
-- name    : QEC.Locality.WeightedBoundaryEdgeRecursion.terminalOwnerCount_mul_budget_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:43:18.470272+00:00
-- url     : https://prove2.me/theorems/fb170869-3059-478a-bb7f-09eb4a3b227e
-- title:
--   Weighted Boundary Edge Recursion: terminal Owner Count mul budget le
-- statement:
--   The Weighted Boundary Edge Recursion construction uses the terminal Owner Count mul budget le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L1245-L1252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/WeightedRefinement.lean#L1245-L1252

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.WeightedBoundaryEdgeRecursion.terminalOwnerCount_mul_budget_le
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.terminalOwnerCount * spineBudget ≤ spineBudget + 2 * boundary.card := by sorry
