-- Prove2me | Theorems.Thm_PI_EF_one_le_level
-- name    : PI.EF.one_le_level
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:58.012083+00:00
-- url     : https://prove2.me/theorems/6371385e-58b5-4f3b-a103-fe3193bacc38
-- title:
--   EF: one le level
-- statement:
--   The EF construction uses the one le level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L12-L13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
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

theorem PI.EF.one_le_level (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by sorry
