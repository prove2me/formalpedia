-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_profile_add
-- name    : QEC.Locality.bkSumPreservingRecurrence_eq_profile_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:06:36.948858+00:00
-- url     : https://prove2.me/theorems/6c70149f-47bf-4ad5-a001-bca24d101031
-- title:
--   Locality: bk Sum Preserving Recurrence eq profile add
-- statement:
--   The Locality construction uses the bk Sum Preserving Recurrence eq profile add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L77-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L77-L88

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrence_eq_profile_add
    (G : ConnectivityGraph ι) (d parent : Nat)
    (hterminal : ¬bkScaleTerminal d parent) :
    bkSumPreservingRecurrence G d parent =
      twoThirdsSeparationProfile G parent +
        (bkAdmissibleChildPairs parent).sup (fun children =>
          if _hchildren : children ∈ bkAdmissibleChildPairs parent then
            bkSumPreservingRecurrence G d children.1 +
              bkSumPreservingRecurrence G d children.2
          else 0) := by sorry
