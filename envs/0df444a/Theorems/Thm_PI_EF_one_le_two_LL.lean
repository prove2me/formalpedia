-- Prove2me | Theorems.Thm_PI_EF_one_le_two_LL
-- name    : PI.EF.one_le_two_LL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:51.569293+00:00
-- url     : https://prove2.me/theorems/bf418af1-527d-4b17-b0d8-27159f4fe387
-- title:
--   EF: one le two LL
-- statement:
--   The EF construction uses the one le two LL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/HalfLeNormLentCtr.lean#L25-L28

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

theorem PI.EF.one_le_two_LL (N : ℕ) [NeZero N] (t : ℝ) : 1 ≤ 2 * LL N t := by sorry
