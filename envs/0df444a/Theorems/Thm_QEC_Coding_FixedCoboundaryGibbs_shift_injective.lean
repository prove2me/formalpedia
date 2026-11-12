-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_shift_injective
-- name    : QEC.Coding.FixedCoboundaryGibbs.shift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:58:20.65108+00:00
-- url     : https://prove2.me/theorems/75c6f7ae-e992-438e-ab70-41bf801b3825
-- title:
--   Fixed Coboundary Gibbs: shift injective
-- statement:
--   The Fixed Coboundary Gibbs construction uses the shift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L96-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L96-L98

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

theorem QEC.Coding.FixedCoboundaryGibbs.shift_injective (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Function.Injective (shift P τ) := by sorry
