-- Prove2me | Theorems.Thm_QEC_Locality_directedEdgeFinset_reverseSymmetric
-- name    : QEC.Locality.directedEdgeFinset_reverseSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:28.529073+00:00
-- url     : https://prove2.me/theorems/f099c4a7-9efd-4c29-9e8d-690484aec106
-- title:
--   Locality: directed Edge Finset reverse Symmetric
-- statement:
--   The graph's full oriented edge set is reverse-symmetric.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L24-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean#L24-L30

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.directedEdgeFinset_reverseSymmetric (G : ConnectivityGraph ι) :
    ReverseSymmetricEdgeSet (directedEdgeFinset G) := by sorry
