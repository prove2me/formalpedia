-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_family_trace
-- name    : QEC.Coding.BDL26CoboundaryContainment.z_family_trace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:16:15.714481+00:00
-- url     : https://prove2.me/theorems/6c22ea70-8a0e-40dc-bfa1-c82cf2752982
-- title:
--   BDL26 Coboundary Containment: z family trace
-- statement:
--   The BDL26 Coboundary Containment construction uses the z family trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L309-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L309-L312

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

theorem QEC.Coding.BDL26CoboundaryContainment.z_family_trace (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    LinearMap.trace ℂ (Qubit.QubitRegister (Physical S n))
      ((gibbs S n β).toOperator * zSelected S n (zFamily S n W)) =
      ((pZ S n β (zFamily S n W) : ℝ) : ℂ) := by sorry
