-- Prove2me | Theorems.Thm_PI_Dv_TIW_asAlgebraHom_mem_span
-- name    : PI.Dv.TIW.asAlgebraHom_mem_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:37.896252+00:00
-- url     : https://prove2.me/theorems/09b2327b-6966-44f0-b8bb-d35930201a16
-- title:
--   TIW: as Algebra Hom mem span
-- statement:
--   The TIW construction uses the as Algebra Hom mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean#L21-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem PI.Dv.TIW.asAlgebraHom_mem_span (τ : Representation K G W) (z : MonoidAlgebra K G) (w : W) :
    τ.asAlgebraHom z w ∈ Submodule.span K (Set.range fun x => τ x w) := by sorry
