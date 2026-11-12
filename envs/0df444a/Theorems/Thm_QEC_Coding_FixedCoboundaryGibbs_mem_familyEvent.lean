-- Prove2me | Theorems.Thm_QEC_Coding_FixedCoboundaryGibbs_mem_familyEvent
-- name    : QEC.Coding.FixedCoboundaryGibbs.mem_familyEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:57:50.22985+00:00
-- url     : https://prove2.me/theorems/01acc73e-13ce-4963-b4f0-c70a931b9e94
-- title:
--   Fixed Coboundary Gibbs: mem family Event
-- statement:
--   The Fixed Coboundary Gibbs construction uses the mem family Event property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L176-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/CoboundaryContainment.lean#L176-L179

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

theorem QEC.Coding.FixedCoboundaryGibbs.mem_familyEvent (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (W : Finset (LinearMap.range P)) (s : LinearMap.range P) :
    s∈familyEvent P W ↔ ∃ τ∈W, hammingSupport τ.val ⊆ hammingSupport s.val := by sorry
