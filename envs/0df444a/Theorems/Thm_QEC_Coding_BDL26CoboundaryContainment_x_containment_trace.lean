-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_x_containment_trace
-- name    : QEC.Coding.BDL26CoboundaryContainment.x_containment_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:16:12.355916+00:00
-- url     : https://prove2.me/theorems/b0455315-1a93-4790-b5b6-deb54969cb42
-- title:
--   BDL26 Coboundary Containment: x containment trace
-- statement:
--   The BDL26 Coboundary Containment construction uses the x containment trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L280-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L280-L283

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

theorem QEC.Coding.BDL26CoboundaryContainment.x_containment_trace (S : OddScale) (n : Nat) (β : ℝ) (τ : XImage S n) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * xSelected S n (xContainment S n τ)) =
      ((pX S n β (xContainment S n τ) : ℝ) : ℂ) := by sorry
