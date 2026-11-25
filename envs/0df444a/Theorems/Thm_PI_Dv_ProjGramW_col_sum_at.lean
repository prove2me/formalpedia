-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_col_sum_at
-- name    : PI.Dv.ProjGramW.col_sum_at
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:50.445926+00:00
-- url     : https://prove2.me/theorems/f079845f-651a-510f-b2cd-04cf07bd1627
-- title:
--   Proj Gram W: col sum at
-- statement:
--   The Proj Gram W construction uses the col sum at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L209-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L209-L218

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

theorem PI.Dv.ProjGramW.col_sum_at {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) :
    (∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k) j0 = algebraMap (𝓞 K) K (r j0) * v j0 := by sorry
