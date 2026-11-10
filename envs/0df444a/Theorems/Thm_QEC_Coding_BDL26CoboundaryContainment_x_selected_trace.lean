-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_selected_trace
-- name    : QEC.Coding.BDL26CoboundaryContainment.x_selected_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:43:50.846684+00:00
-- url     : https://prove2.me/theorems/9eeae4f1-c75e-4462-99b2-ea56ec51ff08
-- title:
--   BDL26 Coboundary Containment: x selected trace
-- statement:
--   Full complex trace, not just its real part.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L266-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L266-L271

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype

theorem QEC.Coding.BDL26CoboundaryContainment.x_selected_trace (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n A) = ((pX S n β A : ℝ) : ℂ) := by sorry
