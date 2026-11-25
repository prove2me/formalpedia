-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idxStd_colOp
-- name    : PI.Dv.ProjGramW.idxStd_colOp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:37.967505+00:00
-- url     : https://prove2.me/theorems/f6477ebf-4628-439e-a95f-958f5926c703
-- title:
--   Proj Gram W: idx Std col Op
-- statement:
--   The Proj Gram W construction uses the idx Std col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L333-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L333-L379

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

theorem PI.Dv.ProjGramW.idxStd_colOp (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (j0 : Fin d) (v : Fin d → K)
    (hv : v j0 ≠ 0) (hdet : (colOp j0 v).det ≠ 0) : idxStd w (colOp j0 v) = vAdd w (v j0) := by sorry
