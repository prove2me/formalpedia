-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_family_mass_le_sum
-- name    : QEC.Coding.FixedCoboundaryGibbs.family_mass_le_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:14:52.153195+00:00
-- url     : https://prove2.me/theorems/bc3c5e07-c324-4b04-b9b7-3b1f0039f9fa
-- title:
--   Fixed Coboundary Gibbs: family mass le sum
-- statement:
--   The Fixed Coboundary Gibbs construction uses the family mass le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L190-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L190-L200

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

theorem QEC.Coding.FixedCoboundaryGibbs.family_mass_le_sum (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (W : Finset (LinearMap.range P)) :
    mass P t (familyEvent P W) ≤ ∑ τ∈W, mass P t (containment P τ) := by sorry
