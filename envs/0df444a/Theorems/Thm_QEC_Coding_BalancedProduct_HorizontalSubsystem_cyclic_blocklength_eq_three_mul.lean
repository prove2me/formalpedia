-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_cyclic_blocklength_eq_three_mul
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.cyclic_blocklength_eq_three_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:38:50.104826+00:00
-- url     : https://prove2.me/theorems/9426a739-8976-4f83-943a-8f395a4a9c21
-- title:
--   Horizontal Subsystem: cyclic blocklength eq three mul
-- statement:
--   A conditional arithmetic identity: if the second qubit block really has twice
--   as many lifted coordinates as the first, then the total has size three times
--   the first block.  The hypotheses do **not** hold for the concrete BE20 LPS
--   Tanner complex, whose check block has `(s - k_L)|X₀|` coordinates.  In
--   particular this lemma must not be used to recover the paper's printed
--   `N = 3|X₁|` formula for that specialization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L663-L672
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L663-L672

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.cyclic_blocklength_eq_three_mul
    {aRow aCol : Type} [Fintype aRow] [Fintype aCol]
    (q edgeCount : Nat) [NeZero q]
    (hHorizontal : q * Fintype.card aCol = edgeCount)
    (hLocalChecks : q * Fintype.card aRow = 2 * edgeCount) :
    Fintype.card
        (LiftedProduct.QubitIndex aRow aCol Unit Unit (CyclicGroup q)) =
      3 * edgeCount := by sorry
