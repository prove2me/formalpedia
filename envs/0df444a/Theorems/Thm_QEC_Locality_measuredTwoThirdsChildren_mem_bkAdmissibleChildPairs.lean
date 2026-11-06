-- Prove2me | Theorems.Thm_QEC_Locality_measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
-- name    : QEC.Locality.measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:24.077911+00:00
-- url     : https://prove2.me/theorems/bfbd7dd6-d1d0-4d7c-8bd6-39d7691207f3
-- title:
--   Locality: measured Two Thirds Children mem bk Admissible Child Pairs
-- statement:
--   The actual #380 split supplies one witness in the admissible-pair maximum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L111-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L111-L122

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.measuredTwoThirdsChildren_mem_bkAdmissibleChildPairs
    (G : ConnectivityGraph ι) (vertices : Finset ι) (hvertices : vertices.Nonempty) :
    ((measuredTwoThirdsLeft G vertices).card,
      (measuredTwoThirdsRight G vertices).card) ∈
        bkAdmissibleChildPairs vertices.card := by sorry
