-- Prove2me | Theorems.Thm_PI_EF_kb_nonneg
-- name    : PI.EF.kb_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:54.427227+00:00
-- url     : https://prove2.me/theorems/92aab8c5-d0ff-490b-96e2-e409248e8223
-- title:
--   EF: kb nonneg
-- statement:
--   The EF construction uses the kb nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L72-L76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
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
open Finset

theorem PI.EF.kb_nonneg {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ kb T y := by sorry
