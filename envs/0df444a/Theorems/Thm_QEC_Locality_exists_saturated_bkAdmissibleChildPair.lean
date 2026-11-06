-- Prove2me | Theorems.Thm_QEC_Locality_exists_saturated_bkAdmissibleChildPair
-- name    : QEC.Locality.exists_saturated_bkAdmissibleChildPair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:12.053481+00:00
-- url     : https://prove2.me/theorems/3de1e3a6-3ae2-4f0e-8c12-a36bdb02a306
-- title:
--   Locality: exists saturated bk Admissible Child Pair
-- statement:
--   Every admissible pair can be enlarged, componentwise, to complementary
--   balanced children.  This is the finite rounding bridge to the source's
--   `alpha_r` and `1-alpha_r` notation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L47-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L47-L66

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

theorem QEC.Locality.exists_saturated_bkAdmissibleChildPair
    {parent : Nat} {children : Nat × Nat} (hparent : 2 ≤ parent)
    (hchildren : children ∈ bkAdmissibleChildPairs parent) :
    ∃ saturated : Nat × Nat,
      children.1 ≤ saturated.1 ∧ children.2 ≤ saturated.2 ∧
      saturated.1 + saturated.2 = parent ∧
      parent ≤ 3 * saturated.1 ∧ parent ≤ 3 * saturated.2 ∧
      3 * saturated.1 ≤ 2 * parent ∧ 3 * saturated.2 ≤ 2 * parent ∧
      saturated.1 < parent ∧ saturated.2 < parent := by sorry
