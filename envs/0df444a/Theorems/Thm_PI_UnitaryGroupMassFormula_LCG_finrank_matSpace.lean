-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_finrank_matSpace
-- name    : PI.UnitaryGroupMassFormula.LCG.finrank_matSpace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:55.325796+00:00
-- url     : https://prove2.me/theorems/4d92df85-ee04-4829-acf5-fc4f3321a69c
-- title:
--   LCG: finrank mat Space
-- statement:
--   The LCG construction uses the finrank mat Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/PackLem.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/PackLem.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_PackLem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Module
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG

theorem PI.UnitaryGroupMassFormula.LCG.finrank_matSpace (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by sorry
