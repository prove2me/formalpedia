-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_family_trace
-- name    : QEC.Coding.BDL26CoboundaryContainment.x_family_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:16:24.257614+00:00
-- url     : https://prove2.me/theorems/79ee31f6-7ebd-482a-81fa-03e73c04861a
-- title:
--   BDL26 Coboundary Containment: x family trace
-- statement:
--   The BDL26 Coboundary Containment construction uses the x family trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L304-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L304-L307

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

theorem QEC.Coding.BDL26CoboundaryContainment.x_family_trace (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (XImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xFamily S n W)) =
      ((pX S n β (xFamily S n W) : ℝ) : ℂ) := by sorry
