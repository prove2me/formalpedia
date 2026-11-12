-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_translated_eq_image
-- name    : QEC.Coding.FixedCoboundaryGibbs.translated_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:56:30.310348+00:00
-- url     : https://prove2.me/theorems/34417262-b519-4201-8b1a-03a720a6cd6c
-- title:
--   Fixed Coboundary Gibbs: translated eq image
-- statement:
--   The Fixed Coboundary Gibbs construction uses the translated eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L114-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L114-L119

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

theorem QEC.Coding.FixedCoboundaryGibbs.translated_eq_image (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) :
    translated P τ = (containment P τ).image (shift P τ) := by sorry
