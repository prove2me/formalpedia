-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_leg
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.leg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:43.120595+00:00
-- url     : https://prove2.me/theorems/dd24ec0a-d1ee-43dc-a3e0-32860d4c0853
-- title:
--   Sc Xu Exists: leg
-- statement:
--   The Sc Xu Exists construction uses the leg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinLeg.lean#L30-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinLeg.lean#L30-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
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

theorem PI.UnitaryGroupMassFormula.ScXuExists.leg (hP : ∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) {up φp uq φq : Fin n → K}
    (hp : Pair O P Λ1 Λ2 a a' α α' up φp) (hq : Pair O P Λ1 Λ2 a a' α α' uq φq)
    (hcp : O.valuation (pr P φp up) = 1) (hcq : O.valuation (pr P φq uq) = 1)
    (hd : O.valuation (pr P φp uq) = 1) :
    ∃ T : GL (Fin n) K, Good O P Λ1 Λ2 a a' α α' T ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ up = uq ∧
      (φq ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = (pr P φq uq / pr P φp up) • (φp ᵥ* P) := by sorry
