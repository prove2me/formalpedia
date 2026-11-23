-- Prove2me | Theorems.Thm_PI_EF_Loc_locC_pos
-- name    : PI.EF.Loc.locC_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:57.022691+00:00
-- url     : https://prove2.me/theorems/a685f928-7b72-4efa-be18-4bf64904b46f
-- title:
--   Loc: loc C pos
-- statement:
--   The Loc construction uses the loc C pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L13-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology

theorem PI.EF.Loc.locC_pos {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by sorry
