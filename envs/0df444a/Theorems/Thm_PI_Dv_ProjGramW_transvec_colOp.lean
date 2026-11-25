-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_transvec_colOp
-- name    : PI.Dv.ProjGramW.transvec_colOp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:18.037437+00:00
-- url     : https://prove2.me/theorems/f57139a8-0bcb-45ec-a9e8-7218e63e0504
-- title:
--   Proj Gram W: transvec col Op
-- statement:
--   The Proj Gram W construction uses the transvec col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L435-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L435-L450

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

theorem PI.Dv.ProjGramW.transvec_colOp {d : ℕ} (i j : Fin d) (hij : i ≠ j) (c : K) :
    Matrix.transvection i j c =
      colOp j (fun p => (if p = j then 1 else 0) + (if p = i then c else 0)) := by sorry
