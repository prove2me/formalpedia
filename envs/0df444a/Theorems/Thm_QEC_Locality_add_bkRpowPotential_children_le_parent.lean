-- Prove2me | Theorems.Thm_QEC_Locality_add_bkRpowPotential_children_le_parent
-- name    : QEC.Locality.add_bkRpowPotential_children_le_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:38:09.103945+00:00
-- url     : https://prove2.me/theorems/b62dae32-2ecf-44cf-9ad2-3163e56f4660
-- title:
--   Locality: add bk Rpow Potential children le parent
-- statement:
--   One complementary balanced split closes the source potential induction step.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L267-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L267-L313

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.add_bkRpowPotential_children_le_parent
    (G : ConnectivityGraph ι)
    {beta c : ℝ} {d parent left right : Nat}
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 0 < d)
    (hparent : 0 < parent) (hsum : left + right = parent)
    (hleftLower : parent ≤ 3 * left) (hleftUpper : 3 * left ≤ 2 * parent)
    (hcharge : (twoThirdsSeparationProfile G parent : ℝ) ≤
      beta * (parent : ℝ) ^ c) :
    (twoThirdsSeparationProfile G parent : ℝ) +
        bkRpowPotential beta c d left + bkRpowPotential beta c d right ≤
      bkRpowPotential beta c d parent := by sorry
