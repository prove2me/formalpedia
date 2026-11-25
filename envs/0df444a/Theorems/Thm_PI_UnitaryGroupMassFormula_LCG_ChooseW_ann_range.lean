-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ChooseW_ann_range
-- name    : PI.UnitaryGroupMassFormula.LCG.ChooseW.ann_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:12.914779+00:00
-- url     : https://prove2.me/theorems/e55e3508-ed43-46ba-84a1-e7c71464dc25
-- title:
--   Choose W: ann range
-- statement:
--   The Choose W construction uses the ann range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L17-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/Choose.lean#L17-L37

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

theorem PI.UnitaryGroupMassFormula.LCG.ChooseW.ann_range (δ : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ha : ∀ z, δ *ᵥ z = 0 → a ⬝ᵥ z = 0) : ∃ t, a = t ᵥ* δ := by sorry
