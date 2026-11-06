-- Prove2me | Theorems.Thm_QEC_Locality_separatorLeftEdges_subset_directed
-- name    : QEC.Locality.separatorLeftEdges_subset_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:21.79761+00:00
-- url     : https://prove2.me/theorems/5f211314-6041-41e6-97b6-b3e16e6b75b7
-- title:
--   Locality: separator Left Edges subset directed
-- statement:
--   Separator allocation preserves the ambient graph-edge invariant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L33-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L33-L37

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.separatorLeftEdges_subset_directed
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (left : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G) :
    separatorLeftEdges edges left ⊆ directedEdgeFinset G := by sorry
