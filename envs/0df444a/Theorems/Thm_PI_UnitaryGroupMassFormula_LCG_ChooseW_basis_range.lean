-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_basis_range
-- name    : PI.UnitaryGroupMassFormula.LCG.ChooseW.basis_range
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:46:31.715542+00:00
-- url     : https://prove2.me/theorems/1e1d0222-20a8-5282-b4c5-6acb7cd790df
-- title:
--   Choose W: basis range
-- statement:
--   The Choose W construction uses the basis range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L56-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L56-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatticeIsometry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_Choose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.ChooseW
variable {K : Type*} [Field K] {n : ℕ}

theorem PI.UnitaryGroupMassFormula.LCG.ChooseW.basis_range (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by sorry
