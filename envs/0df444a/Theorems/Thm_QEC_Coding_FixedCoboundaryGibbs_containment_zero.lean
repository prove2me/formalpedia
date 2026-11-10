-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_zero
-- name    : QEC.Coding.FixedCoboundaryGibbs.containment_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:14:44.034933+00:00
-- url     : https://prove2.me/theorems/e9626666-5c6e-4449-b0cd-01c02de3f539
-- title:
--   Fixed Coboundary Gibbs: containment zero
-- statement:
--   The Fixed Coboundary Gibbs construction uses the containment zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L161-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L161-L164

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

theorem QEC.Coding.FixedCoboundaryGibbs.containment_zero (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K) :
    containment P 0 = Finset.univ := by sorry
