-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idxStd_list
-- name    : PI.Dv.ProjGramW.idxStd_list
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:34.34235+00:00
-- url     : https://prove2.me/theorems/d09777c1-51b0-5794-b9ee-dda6a142fcc1
-- title:
--   Proj Gram W: idx Std list
-- statement:
--   The Proj Gram W construction uses the idx Std list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L461-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L461-L471

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

theorem PI.Dv.ProjGramW.idxStd_list (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ}
    (L : List (Matrix.TransvectionStruct (Fin d) K)) :
    idxStd w (L.map Matrix.TransvectionStruct.toMatrix).prod = 0 := by sorry
