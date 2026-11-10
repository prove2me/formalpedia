-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_selected_trace
-- name    : QEC.Coding.BDL26CoboundaryContainment.z_selected_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:45:03.54564+00:00
-- url     : https://prove2.me/theorems/1c79eb52-0cb3-4a05-b667-58333fbbbb76
-- title:
--   BDL26 Coboundary Containment: z selected trace
-- statement:
--   The BDL26 Coboundary Containment construction uses the z selected trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L273-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L273-L278

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

theorem QEC.Coding.BDL26CoboundaryContainment.z_selected_trace (S : OddScale) (n : Nat) (β : ℝ) (A : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n A) = ((pZ S n β A : ℝ) : ℂ) := by sorry
