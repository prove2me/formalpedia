-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_isAdmissible_rankOneGL
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.isAdmissible_rankOneGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:34.664521+00:00
-- url     : https://prove2.me/theorems/d227c9f9-039e-4123-8e38-d6e4df6339d6
-- title:
--   Sc Xu Exists: is Admissible rank One GL
-- statement:
--   The Sc Xu Exists construction uses the is Admissible rank One GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L165-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L165-L204

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
variable {O P Λ1 Λ2 a a' α α'}

theorem PI.UnitaryGroupMassFormula.ScXuExists.isAdmissible_rankOneGL (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) (w γ : Fin n → K) (c d : K)
    (h : c + d + c * d * ((γ ᵥ* P) ⬝ᵥ w) = 0) (hc : c ∈ O) (hd : d ∈ O) (hw : w ∈ Λ1) (hγ : γ ∈ Λ2)
    (hwα : ∀ i, pr P (α i) w = 0 ∧ pr P (α' i) w = 0) (hγa : ∀ i, pr P γ (a i) = 0 ∧ pr P γ (a' i) = 0) :
    Good O P Λ1 Λ2 a a' α α' (rankOneUnitGL w (γ ᵥ* P) c d h) := by sorry
