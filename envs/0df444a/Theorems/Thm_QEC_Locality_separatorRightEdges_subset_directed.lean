-- Prove2me | Theorems.Thm_QEC_Locality_separatorRightEdges_subset_directed
-- name    : QEC.Locality.separatorRightEdges_subset_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:42:54.893529+00:00
-- url     : https://prove2.me/theorems/14478ee7-5802-416e-b73d-b24103c40e9c
-- title:
--   Locality: separator Right Edges subset directed
-- statement:
--   Complementary separator allocation preserves the ambient graph-edge invariant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L40-L44

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.separatorRightEdges_subset_directed
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (left : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G) :
    separatorRightEdges edges left ⊆ directedEdgeFinset G := by sorry
