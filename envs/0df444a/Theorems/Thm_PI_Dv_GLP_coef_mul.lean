-- Prove2me | Theorems.Thm_PI_Dv_GLP_coef_mul
-- name    : PI.Dv.GLP.coef_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:28.006006+00:00
-- url     : https://prove2.me/theorems/23416f84-bf82-44a9-bbf2-796f71b805d6
-- title:
--   GLP: coef mul
-- statement:
--   The GLP construction uses the coef mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L181-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L181-L195

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLP.coef_mul [CharZero K] (T : GoodSet K G) (s t : T.S) (z : G) :
    ∑ x : G, cS T s x * cS T t (x⁻¹ * z) = if s = t then cS T s z else 0 := by sorry
