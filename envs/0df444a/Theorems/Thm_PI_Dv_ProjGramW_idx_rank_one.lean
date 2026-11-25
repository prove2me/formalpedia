-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idx_rank_one
-- name    : PI.Dv.ProjGramW.idx_rank_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:43.412404+00:00
-- url     : https://prove2.me/theorems/c59da9df-f2cd-4251-bd07-df79f88e1b54
-- title:
--   Proj Gram W: idx rank one
-- statement:
--   The Proj Gram W construction uses the idx rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L308-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L308-L331

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

theorem PI.Dv.ProjGramW.idx_rank_one (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {c : K} (hc : c ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {(1 : K)}) (Submodule.span (𝓞 K) {c}) = vAdd w c := by sorry
