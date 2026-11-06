-- Prove2me | Theorems.Thm_QEC_Locality_zero_zero_mem_bkAdmissibleChildPairs
-- name    : QEC.Locality.zero_zero_mem_bkAdmissibleChildPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:01.917702+00:00
-- url     : https://prove2.me/theorems/856e9d73-aed0-45c6-8302-657ddf78ed67
-- title:
--   Locality: zero zero mem bk Admissible Child Pairs
-- statement:
--   The Locality construction uses the zero zero mem bk Admissible Child Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L41-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L41-L44

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.zero_zero_mem_bkAdmissibleChildPairs {parent : Nat} (hparent : 0 < parent) :
    (0, 0) ∈ bkAdmissibleChildPairs parent := by sorry
