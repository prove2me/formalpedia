-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idxStd_one
-- name    : PI.Dv.ProjGramW.idxStd_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:11.66584+00:00
-- url     : https://prove2.me/theorems/cf78ee51-3808-4031-8ce7-e0173fbe2daf
-- title:
--   Proj Gram W: idx Std one
-- statement:
--   The Proj Gram W construction uses the idx Std one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L170-L174

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

theorem PI.Dv.ProjGramW.idxStd_one (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) :
    idxStd w (1 : Matrix (Fin d) (Fin d) K) = 0 := by sorry
