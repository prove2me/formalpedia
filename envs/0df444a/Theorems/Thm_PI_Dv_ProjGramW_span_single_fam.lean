-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_span_single_fam
-- name    : PI.Dv.ProjGramW.span_single_fam
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:33.665009+00:00
-- url     : https://prove2.me/theorems/56338168-4b4f-5a81-ad95-50e75c65d561
-- title:
--   Proj Gram W: span single fam
-- statement:
--   The Proj Gram W construction uses the span single fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L223-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L223-L233

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

theorem PI.Dv.ProjGramW.span_single_fam {d : ℕ} (j0 : Fin d) (u : Fin d → K) (hu : ∀ k, k ≠ j0 → u k = 0) :
    Submodule.span (𝓞 K) (Set.range u) = Submodule.span (𝓞 K) {u j0} := by sorry
