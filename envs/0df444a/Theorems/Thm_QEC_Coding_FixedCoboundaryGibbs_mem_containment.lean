-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_mem_containment
-- name    : QEC.Coding.FixedCoboundaryGibbs.mem_containment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T02:44:58.270243+00:00
-- url     : https://prove2.me/theorems/41e4d7ed-0ce0-419e-9d77-d31d61b3f323
-- title:
--   Fixed Coboundary Gibbs: mem containment
-- statement:
--   The Fixed Coboundary Gibbs construction uses the mem containment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L105-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L105-L108

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

theorem QEC.Coding.FixedCoboundaryGibbs.mem_containment (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ s : LinearMap.range P) :
    s∈containment P τ ↔ hammingSupport τ.val ⊆ hammingSupport s.val := by sorry
