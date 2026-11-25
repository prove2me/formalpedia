-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_sum_right__14e5aa179fb6
-- name    : P2M_PI_Dv_GLP_majAt_sum_right__14e5aa179fb6
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:25.08553+00:00
-- url     : https://prove2.me/theorems/64aa4186-ace3-487b-bf9b-402705b02cb6
-- title:
--   P2 M PI Dv GLP maj At sum right  14e5aa179fb6: P2 M PI Dv GLP maj At sum right  14e5aa179fb6
-- statement:
--   The P2 M PI Dv GLP maj At sum right  14e5aa179fb6 construction uses the P2 M PI Dv GLP maj At sum right  14e5aa179fb6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L71-L73

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

theorem P2M_PI_Dv_GLP_majAt_sum_right__14e5aa179fb6 {α : Type} (s : Finset α) (f : α → V) (x : V) :
    majAt b X v x (∑ i ∈ s, f i) = ∑ i ∈ s, majAt b X v x (f i) := by sorry

alias «PI».«Dv».«GLP».«majAt_sum_right'» := P2M_PI_Dv_GLP_majAt_sum_right__14e5aa179fb6
