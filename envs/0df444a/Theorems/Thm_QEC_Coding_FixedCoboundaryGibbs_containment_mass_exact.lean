-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_containment_mass_exact
-- name    : QEC.Coding.FixedCoboundaryGibbs.containment_mass_exact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T02:08:24.981546+00:00
-- url     : https://prove2.me/theorems/05270a35-0d26-4f9b-92c3-875815a6b240
-- title:
--   Fixed Coboundary Gibbs: containment mass exact
-- statement:
--   Exact normalized translated mass for EVERY real temperature.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L144-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L144-L152

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

theorem QEC.Coding.FixedCoboundaryGibbs.containment_mass_exact (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (t : ℝ) (τ : LinearMap.range P) :
    mass P t (containment P τ) =
      Real.exp (-t*(HammingWeight τ.val : ℝ)) * mass P t (translated P τ) := by sorry
