-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_inv__221800ad7a3f
-- name    : P2M_PI_Dv_GLP_majAt_inv__221800ad7a3f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:18.725962+00:00
-- url     : https://prove2.me/theorems/2a31cad8-4923-4e85-8efe-fc6369d6e01a
-- title:
--   P2 M PI Dv GLP maj At inv  221800ad7a3f: P2 M PI Dv GLP maj At inv  221800ad7a3f
-- statement:
--   The P2 M PI Dv GLP maj At inv  221800ad7a3f construction uses the P2 M PI Dv GLP maj At inv  221800ad7a3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L92-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L92-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
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
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem P2M_PI_Dv_GLP_majAt_inv__221800ad7a3f [NumberField.IsTotallyComplex K] (g : V →ₗ[K] V)
    (hg : ∀ x, normAt b X v (g x) = normAt b X v x) (x y : V) :
    majAt b X v (g x) (g y) = majAt b X v x y := by sorry

alias «PI».«Dv».«GLP».«majAt_inv'» := P2M_PI_Dv_GLP_majAt_inv__221800ad7a3f
