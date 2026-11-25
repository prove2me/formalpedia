-- Prove2me | Theorems.Thm_PI_Residue_wt_apply
-- name    : PI.Residue.wt_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:36.096712+00:00
-- url     : https://prove2.me/theorems/1821f094-5818-4d4d-a637-338b993395fc
-- title:
--   Residue: wt apply
-- statement:
--   The Residue construction uses the wt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NnrealOfEnnreal.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/NnrealOfEnnreal.lean#L16-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_HeckeLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_NnrealOfEnnreal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField
open scoped ENNReal NNReal

theorem PI.Residue.wt_apply (s : ℝ) (n : ℕ) : wt s n = (((n : ℝ≥0) ^ (-s) : ℝ≥0) : ℝ≥0∞) := by sorry
