-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_support_remove
-- name    : QEC.Coding.FixedCoboundaryGibbs.support_remove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:13:59.798477+00:00
-- url     : https://prove2.me/theorems/ca5f6f79-8e72-4cc9-9535-a3b975944997
-- title:
--   Fixed Coboundary Gibbs: support remove
-- statement:
--   Binary cancellation removes exactly the contained coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L23-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L23-L67

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

theorem QEC.Coding.FixedCoboundaryGibbs.support_remove (s τ : Word (ZMod 2) K)
    (h : hammingSupport τ ⊆ hammingSupport s) :
    hammingSupport (s+τ) = hammingSupport s \ hammingSupport τ := by sorry
