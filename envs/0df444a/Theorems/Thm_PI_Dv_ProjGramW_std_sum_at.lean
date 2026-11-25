-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_std_sum_at
-- name    : PI.Dv.ProjGramW.std_sum_at
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:53.359708+00:00
-- url     : https://prove2.me/theorems/1e640cdf-24a4-4ed5-9ee3-cf1d38d8be33
-- title:
--   Proj Gram W: std sum at
-- statement:
--   The Proj Gram W construction uses the std sum at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L204-L207

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.std_sum_at {d : ℕ} (j0 : Fin d) (r : Fin d → 𝓞 K) :
    (∑ k, r k • stdE (K := K) d k) j0 = algebraMap (𝓞 K) K (r j0) := by sorry
