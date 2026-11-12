-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_containment_trace_bound
-- name    : QEC.Coding.BDL26CoboundaryContainment.x_containment_trace_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:00:36.988717+00:00
-- url     : https://prove2.me/theorems/e06aa0f1-d58a-486a-ae87-889d13e2a06b
-- title:
--   BDL26 Coboundary Containment: x containment trace bound
-- statement:
--   The BDL26 Coboundary Containment construction uses the x containment trace bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L290-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L290-L295

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

theorem QEC.Coding.BDL26CoboundaryContainment.x_containment_trace_bound (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    (LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xContainment S n τ))).re ≤
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by sorry
