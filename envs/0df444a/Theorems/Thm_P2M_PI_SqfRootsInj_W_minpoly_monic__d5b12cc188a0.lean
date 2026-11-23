-- Prove2me | Theorems.Thm_P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
-- name    : P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:26.200046+00:00
-- url     : https://prove2.me/theorems/ab42375d-58db-4bc5-93dd-ac1381e06ed5
-- title:
--   P2 M PI Sqf Roots Inj W minpoly monic  d5b12cc188a0: P2 M PI Sqf Roots Inj W minpoly monic  d5b12cc188a0
-- statement:
--   The P2 M PI Sqf Roots Inj W minpoly monic  d5b12cc188a0 construction uses the P2 M PI Sqf Roots Inj W minpoly monic  d5b12cc188a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreeRootsInjective/CardLeSumOfCover.lean#L38-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_DivCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_CardLeSumOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab

theorem P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0 {g : ℕ} [Fact g.Prime] (w : Fbar g) : (minpoly (ZMod g) w).Monic := by sorry

alias «PI».«SqfRootsInj».«W».«minpoly_monic'» := P2M_PI_SqfRootsInj_W_minpoly_monic__d5b12cc188a0
