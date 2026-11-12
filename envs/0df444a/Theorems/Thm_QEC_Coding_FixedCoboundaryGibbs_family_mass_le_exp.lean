-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_family_mass_le_exp
-- name    : QEC.Coding.FixedCoboundaryGibbs.family_mass_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:43:58.09887+00:00
-- url     : https://prove2.me/theorems/abb8e777-c6b1-4c49-a11d-390f7b22e46e
-- title:
--   Fixed Coboundary Gibbs: family mass le exp
-- statement:
--   The Fixed Coboundary Gibbs construction uses the family mass le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L202-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L202-L206

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

theorem QEC.Coding.FixedCoboundaryGibbs.family_mass_le_exp (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (W : Finset (LinearMap.range P)) :
    mass P t (familyEvent P W) ≤ ∑ τ∈W, Real.exp (-t*(HammingWeight τ.val : ℝ)) := by sorry
