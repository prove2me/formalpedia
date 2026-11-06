-- Prove2me | Theorems.Thm_QEC_Locality_bkTwoThirdsChildScale_mono
-- name    : QEC.Locality.bkTwoThirdsChildScale_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:07.010584+00:00
-- url     : https://prove2.me/theorems/04296232-4ab5-4742-806c-fe77c34fa22b
-- title:
--   Locality: bk Two Thirds Child Scale mono
-- statement:
--   The Locality construction uses the bk Two Thirds Child Scale mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L157-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/RecursiveSeparator.lean#L157-L160

import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkTwoThirdsChildScale_mono {small large : Nat} (h : small ≤ large) :
    bkTwoThirdsChildScale small ≤ bkTwoThirdsChildScale large := by sorry
