-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_slice_eq
-- name    : PI.TwistedEisensteinNonvanishing.W.sum_slice_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:25.524994+00:00
-- url     : https://prove2.me/theorems/f33672af-ff0b-4155-accd-e47e78c23255
-- title:
--   W: sum slice eq
-- statement:
--   The W construction uses the sum slice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/SumSliceEq.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/SumSliceEq.lean#L46-L52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.TwistedEisensteinNonvanishing.W.sum_slice_eq (k : ι) (S : ι → Finset E) (T T' : Finset E) (F G : (ι → E) → K) (α : K)
    (h : ∀ t : ι → E, ∑ u ∈ T, F (update t k u) = α * ∑ u ∈ T', G (update t k u)) :
    ∑ t ∈ Fintype.piFinset (update S k T), F t = α * ∑ t ∈ Fintype.piFinset (update S k T'), G t := by sorry
