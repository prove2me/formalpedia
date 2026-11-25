-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idx_int
-- name    : PI.Dv.ProjGramW.idx_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:28.065212+00:00
-- url     : https://prove2.me/theorems/8dcc97ee-2e6e-5370-8096-f8b9270071ce
-- title:
--   Proj Gram W: idx int
-- statement:
--   The Proj Gram W construction uses the idx int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L242-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L242-L306

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

theorem PI.Dv.ProjGramW.idx_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {r : 𝓞 K} (hr : r ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {y}) (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y}) =
      vAdd w (algebraMap (𝓞 K) K r) := by sorry
