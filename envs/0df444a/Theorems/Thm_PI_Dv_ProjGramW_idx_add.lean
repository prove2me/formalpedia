-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_idx_add
-- name    : PI.Dv.ProjGramW.idx_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:37.081815+00:00
-- url     : https://prove2.me/theorems/8066062e-8bb3-4361-8403-e93a0800dc4d
-- title:
--   Proj Gram W: idx add
-- statement:
--   The Proj Gram W construction uses the idx add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L61-L65

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

theorem PI.Dv.ProjGramW.idx_add (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {M N P : Submodule (𝓞 K) V}
    (hM : M.FG) (hN : N.FG) (hP : P.FG) (hMN : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hPN : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P := by sorry
