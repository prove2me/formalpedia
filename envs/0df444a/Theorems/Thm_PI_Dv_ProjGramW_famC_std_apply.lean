-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_famC_std_apply
-- name    : PI.Dv.ProjGramW.famC_std_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:38.306093+00:00
-- url     : https://prove2.me/theorems/03b3e15d-c2b8-4cd5-a5cc-9103b61be2c2
-- title:
--   Proj Gram W: fam C std apply
-- statement:
--   The Proj Gram W construction uses the fam C std apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L179-L181

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

theorem PI.Dv.ProjGramW.famC_std_apply {d : ℕ} (C : Matrix (Fin d) (Fin d) K) (j i : Fin d) :
    famC (stdE (K := K) d) C j i = C i j := by sorry
