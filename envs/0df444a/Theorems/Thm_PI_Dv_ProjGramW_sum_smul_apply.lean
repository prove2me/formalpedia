-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_sum_smul_apply
-- name    : PI.Dv.ProjGramW.sum_smul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:37.783937+00:00
-- url     : https://prove2.me/theorems/bcf0797b-a809-489c-b240-f114a8d0a587
-- title:
--   Proj Gram W: sum smul apply
-- statement:
--   The Proj Gram W construction uses the sum smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L183-L186

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

theorem PI.Dv.ProjGramW.sum_smul_apply {d : ℕ} (r : Fin d → 𝓞 K) (u : Fin d → (Fin d →₀ K)) (i : Fin d) :
    (∑ k, r k • u k) i = ∑ k, r k • u k i := by sorry
