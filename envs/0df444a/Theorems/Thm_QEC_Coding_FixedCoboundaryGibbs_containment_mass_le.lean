-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_le
-- name    : QEC.Coding.FixedCoboundaryGibbs.containment_mass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:09:51.718756+00:00
-- url     : https://prove2.me/theorems/bcaba433-cca8-4aab-91f4-624d932f9f3d
-- title:
--   Fixed Coboundary Gibbs: containment mass le
-- statement:
--   The Fixed Coboundary Gibbs construction uses the containment mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L154-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L154-L159

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype

theorem QEC.Coding.FixedCoboundaryGibbs.containment_mass_le (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ : LinearMap.range P) :
    mass P t (containment P τ) ≤ Real.exp (-t*(HammingWeight τ.val : ℝ)) := by sorry
