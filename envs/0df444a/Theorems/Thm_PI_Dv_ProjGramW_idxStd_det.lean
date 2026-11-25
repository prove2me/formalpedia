-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idxStd_det
-- name    : PI.Dv.ProjGramW.idxStd_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:40.555906+00:00
-- url     : https://prove2.me/theorems/a20ab37d-b77d-4e33-a9c3-d18bbcfdeeb3
-- title:
--   Proj Gram W: idx Std det
-- statement:
--   The Proj Gram W construction uses the idx Std det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L473-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L473-L490

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

theorem PI.Dv.ProjGramW.idxStd_det (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : idxStd w C = vAdd w C.det := by sorry
