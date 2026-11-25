-- Prove2me | Theorems.Thm_PI_EF_sum_DZ_eq
-- name    : PI.EF.sum_DZ_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:54.829932+00:00
-- url     : https://prove2.me/theorems/7e8af640-695d-5b02-9925-65f7bb87857d
-- title:
--   EF: sum DZ eq
-- statement:
--   The EF construction uses the sum DZ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L38-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogWindowLe.lean#L38-L109

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogWindowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]

theorem PI.EF.sum_DZ_eq {χ : DirichletCharacter ℂ N} (t : ℝ)
    (hfin : (DZ χ t).Finite) (F : ℂ → ℂ) :
    ∃ E : Finset ℂ, (∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) ∧
      ∑ᶠ ρ ∈ DZ χ t, F ρ = ∑ᶠ ρ ∈ ZerosNear χ t, F ρ + ∑ ρ ∈ E, F ρ +
        (open Classical in if (0 : ℂ) ∈ DZ χ t then F 0 else 0) := by sorry
