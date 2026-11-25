-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_colOp_diag
-- name    : PI.Dv.ProjGramW.colOp_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:40.9088+00:00
-- url     : https://prove2.me/theorems/c76cd6dd-af97-41d7-adf5-172cac656825
-- title:
--   Proj Gram W: col Op diag
-- statement:
--   The Proj Gram W construction uses the col Op diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L381-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L381-L392

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

theorem PI.Dv.ProjGramW.colOp_diag {d : ℕ} (k : Fin d) (c : K) :
    colOp k (fun i => if i = k then c else 0) = Matrix.diagonal (fun m => if m = k then c else 1) := by sorry
