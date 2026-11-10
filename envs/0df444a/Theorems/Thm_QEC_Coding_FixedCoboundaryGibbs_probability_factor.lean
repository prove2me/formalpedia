-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_probability_factor
-- name    : QEC.Coding.FixedCoboundaryGibbs.probability_factor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T04:14:19.309194+00:00
-- url     : https://prove2.me/theorems/f1df1c4d-0176-490b-baef-7efb6ea0cdf2
-- title:
--   Fixed Coboundary Gibbs: probability factor
-- statement:
--   The exact probability ratio uses the SAME original partition function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L131-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L131-L141

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

theorem QEC.Coding.FixedCoboundaryGibbs.probability_factor (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ s : LinearMap.range P) (hs : s∈containment P τ) :
    CSSGibbs.rowProbability P t s =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * CSSGibbs.rowProbability P t (shift P τ s) := by sorry
