-- Prove2me | Theorems.Thm_QEC_Locality_bkAdmissibleChildPairs_mono
-- name    : QEC.Locality.bkAdmissibleChildPairs_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:41.590124+00:00
-- url     : https://prove2.me/theorems/fa47de52-fca3-4d8b-bb9a-10b6868a112f
-- title:
--   Locality: bk Admissible Child Pairs mono
-- statement:
--   The Locality construction uses the bk Admissible Child Pairs mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L188-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L188-L195

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkAdmissibleChildPairs_mono {small large : Nat} (hscale : small ≤ large) :
    bkAdmissibleChildPairs small ⊆ bkAdmissibleChildPairs large := by sorry
