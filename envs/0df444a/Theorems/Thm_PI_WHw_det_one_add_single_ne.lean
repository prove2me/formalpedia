-- Prove2me | Theorems.Thm_PI_WHw_det_one_add_single_ne
-- name    : PI.WHw.det_one_add_single_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:01.746147+00:00
-- url     : https://prove2.me/theorems/5791ebe9-5416-49f8-a36a-676234357a10
-- title:
--   WHw: det one add single ne
-- statement:
--   The WHw construction uses the det one add single ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L62-L75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WHw.det_one_add_single_ne {N : ℕ} (a b : Fin N) (n : ℕ) :
    (1 + Matrix.single a b (n : ℂ)).det ≠ 0 := by sorry
