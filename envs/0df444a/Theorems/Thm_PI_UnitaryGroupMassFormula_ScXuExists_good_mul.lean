-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_good_mul
-- name    : PI.UnitaryGroupMassFormula.ScXuExists.good_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:25.14464+00:00
-- url     : https://prove2.me/theorems/22590f2c-203d-41fc-98b3-eff66d5605a9
-- title:
--   Sc Xu Exists: good mul
-- statement:
--   The Sc Xu Exists construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L137-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinBase.lean#L137-L162

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

theorem PI.UnitaryGroupMassFormula.ScXuExists.good_mul {S T : GL (Fin n) K} (hS : Good O P Λ1 Λ2 a a' α α' S)
    (hT : Good O P Λ1 Λ2 a a' α α' T) : Good O P Λ1 Λ2 a a' α α' (S * T) := by sorry
