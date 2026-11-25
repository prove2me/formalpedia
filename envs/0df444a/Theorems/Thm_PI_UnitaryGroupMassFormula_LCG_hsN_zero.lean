-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_hsN_zero
-- name    : PI.UnitaryGroupMassFormula.LCG.hsN_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:40:18.381298+00:00
-- url     : https://prove2.me/theorems/67191e9d-62fd-43c3-bbe3-4683ad7057b7
-- title:
--   LCG: hs N zero
-- statement:
--   The LCG construction uses the hs N zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/LatCountAllOf.lean#L12-L13

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_LatCountAllOf
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
open PI.LatCountG

theorem PI.UnitaryGroupMassFormula.LCG.hsN_zero {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by sorry
