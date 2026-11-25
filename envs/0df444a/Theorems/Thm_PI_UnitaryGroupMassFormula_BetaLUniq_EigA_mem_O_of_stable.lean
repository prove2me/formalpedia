-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_BetaLUniq_EigA_mem_O_of_stable
-- name    : PI.UnitaryGroupMassFormula.BetaLUniq.EigA.mem_O_of_stable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:16.068373+00:00
-- url     : https://prove2.me/theorems/ef83cdab-98a5-47f8-bea2-c99861e95df0
-- title:
--   Eig A: mem O of stable
-- statement:
--   The Eig A construction uses the mem O of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BetaUniqueness/EqZeroOfNormLtOne.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BetaUniqueness/EqZeroOfNormLtOne.lean#L50-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]

theorem PI.UnitaryGroupMassFormula.BetaLUniq.EigA.mem_O_of_stable (I : Submodule (𝓞 E) E) (hI : I ≠ ⊥) (hfg : I.FG) (x : E)
    (hx : ∀ c ∈ I, x * c ∈ I) : InO x := by sorry
