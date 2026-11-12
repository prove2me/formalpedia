-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_mass_exact
-- name    : QEC.Coding.BDL26CoboundaryContainment.z_mass_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:59:29.435002+00:00
-- url     : https://prove2.me/theorems/d4d6898c-8fb0-469d-af2a-d485f9c1bf27
-- title:
--   BDL26 Coboundary Containment: z mass exact
-- statement:
--   The BDL26 Coboundary Containment construction uses the z mass exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L237-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L237-L241

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CoboundaryContainment
open Classical Semantics BDL26FiniteTannerSquare BDL26CSSHamiltonian BDL26TwoSectorBadProjector
open scoped BigOperators
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.xImageFintype
attribute [local instance] QEC.Coding.BDL26CoboundaryContainment.zImageFintype

theorem QEC.Coding.BDL26CoboundaryContainment.z_mass_exact (S : OddScale) (n : Nat) (β : ℝ) (τ : ZImage S n) :
    pZ S n β (zContainment S n τ) =
      Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) *
        pZ S n β (FixedCoboundaryGibbs.translated (xSyndrome S n) τ) := by sorry
