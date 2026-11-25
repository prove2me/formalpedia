-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_colOp_col
-- name    : PI.Dv.ProjGramW.colOp_col
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:26.574608+00:00
-- url     : https://prove2.me/theorems/437ec0ae-a86c-4f74-b52c-a4c50f8a14f8
-- title:
--   Proj Gram W: col Op col
-- statement:
--   The Proj Gram W construction uses the col Op col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L188-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L188-L195

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

theorem PI.Dv.ProjGramW.colOp_col {d : ℕ} (j0 : Fin d) (v : Fin d → K) (k : Fin d) (hk : k ≠ j0) :
    famC (stdE (K := K) d) (colOp j0 v) k = stdE d k := by sorry
