-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_algebraMap_eq_zero
-- name    : PI.Dv.ProjGramW.algebraMap_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:39.214971+00:00
-- url     : https://prove2.me/theorems/2a0c88f3-7bad-4d61-8b35-b0f9e7d4d5a7
-- title:
--   Proj Gram W: algebra Map eq zero
-- statement:
--   The Proj Gram W construction uses the algebra Map eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L220-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L220-L221

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

theorem PI.Dv.ProjGramW.algebraMap_eq_zero {r : 𝓞 K} (h : algebraMap (𝓞 K) K r = 0) : r = 0 := by sorry
