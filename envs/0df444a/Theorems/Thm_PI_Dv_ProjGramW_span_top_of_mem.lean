-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_span_top_of_mem
-- name    : PI.Dv.ProjGramW.span_top_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:22.269375+00:00
-- url     : https://prove2.me/theorems/52130a1c-6edf-4827-be31-2bdeb68cd4ed
-- title:
--   Proj Gram W: span top of mem
-- statement:
--   The Proj Gram W construction uses the span top of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L235-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L235-L237

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

theorem PI.Dv.ProjGramW.span_top_of_mem {Z : Submodule (𝓞 K) K} {z : K} (hz : z ∈ Z) (hz0 : z ≠ 0) :
    Submodule.span K (Z : Set K) = ⊤ := by sorry
