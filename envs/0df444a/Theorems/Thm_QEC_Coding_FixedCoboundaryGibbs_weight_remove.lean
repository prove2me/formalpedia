-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_weight_remove
-- name    : QEC.Coding.FixedCoboundaryGibbs.weight_remove
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:13:14.253275+00:00
-- url     : https://prove2.me/theorems/1704667e-a854-498a-af25-0984f2b7589e
-- title:
--   Fixed Coboundary Gibbs: weight remove
-- statement:
--   Exact energy removal, not merely a Hamming triangle inequality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L70-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L70-L75

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

theorem QEC.Coding.FixedCoboundaryGibbs.weight_remove (s τ : Word (ZMod 2) K)
    (h : hammingSupport τ ⊆ hammingSupport s) :
    HammingWeight s = HammingWeight τ + HammingWeight (s+τ) := by sorry
