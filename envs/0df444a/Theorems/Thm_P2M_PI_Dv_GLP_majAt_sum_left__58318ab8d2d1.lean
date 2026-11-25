-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_sum_left__58318ab8d2d1
-- name    : P2M_PI_Dv_GLP_majAt_sum_left__58318ab8d2d1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:19.477448+00:00
-- url     : https://prove2.me/theorems/85489577-94b5-4a4a-b17c-55f87d1dd5e9
-- title:
--   P2 M PI Dv GLP maj At sum left  58318ab8d2d1: P2 M PI Dv GLP maj At sum left  58318ab8d2d1
-- statement:
--   The P2 M PI Dv GLP maj At sum left  58318ab8d2d1 construction uses the P2 M PI Dv GLP maj At sum left  58318ab8d2d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L67-L69

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

theorem P2M_PI_Dv_GLP_majAt_sum_left__58318ab8d2d1 {α : Type} (s : Finset α) (f : α → V) (y : V) :
    majAt b X v (∑ i ∈ s, f i) y = ∑ i ∈ s, majAt b X v (f i) y := by sorry

alias «PI».«Dv».«GLP».«majAt_sum_left'» := P2M_PI_Dv_GLP_majAt_sum_left__58318ab8d2d1
