-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CoboundaryContainment_z_family_le
-- name    : QEC.Coding.BDL26CoboundaryContainment.z_family_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T04:15:36.400971+00:00
-- url     : https://prove2.me/theorems/062e6c00-d9a1-4332-a018-529d79930028
-- title:
--   BDL26 Coboundary Containment: z family le
-- statement:
--   The BDL26 Coboundary Containment construction uses the z family le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L255-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L255-L257

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

theorem QEC.Coding.BDL26CoboundaryContainment.z_family_le (S : OddScale) (n : Nat) (β : ℝ) (W : Finset (ZImage S n)) :
    pZ S n β (zFamily S n W) ≤ ∑ τ∈W, Real.exp (-(2*β)*(HammingWeight τ.val : ℝ)) := by sorry
