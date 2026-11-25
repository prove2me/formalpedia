-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_matVec_sub
-- name    : PI.UnitaryGroupMassFormula.LCG.matVec_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:56.391864+00:00
-- url     : https://prove2.me/theorems/c076590f-3c2b-47df-8b9b-9e23e1943ea1
-- title:
--   LCG: mat Vec sub
-- statement:
--   The LCG construction uses the mat Vec sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/PackLem.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/PackLem.lean#L17-L19

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

theorem PI.UnitaryGroupMassFormula.LCG.matVec_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : matVec (A - B) = matVec A - matVec B := by sorry
