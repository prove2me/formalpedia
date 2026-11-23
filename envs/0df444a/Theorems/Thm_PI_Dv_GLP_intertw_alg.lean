-- Prove2me | Theorems.Thm_PI_Dv_GLP_intertw_alg
-- name    : PI.Dv.GLP.intertw_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:26.562801+00:00
-- url     : https://prove2.me/theorems/be0b3485-bf19-41ed-8908-3c6df28d1941
-- title:
--   GLP: intertw alg
-- statement:
--   The GLP construction uses the intertw alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L12-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.GLP.intertw_alg {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (f : V →ₗ[K] W)
    (hf : ∀ g x, f (ρ g x) = σ g (f x)) (a : MonoidAlgebra K G) (x : V) :
    f (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (f x) := by sorry
