-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_perm_range
-- name    : PI.TwistedEisensteinNonvanishing.W.perm_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:31.471952+00:00
-- url     : https://prove2.me/theorems/f97e41b7-c7cb-4fa3-871b-bff82bac1e63
-- title:
--   W: perm range
-- statement:
--   The W construction uses the perm range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L16-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
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
open Loc LocE
variable {K : Type} [Field K]

theorem PI.TwistedEisensteinNonvanishing.W.perm_range (M : ℕ) (f : ℕ → ℕ) (hf : ∀ i < M, f i < M)
    (hinj : ∀ i < M, ∀ j < M, f i = f j → i = j) (g : ℕ → K) :
    ∑ i ∈ Finset.range M, g (f i) = ∑ i ∈ Finset.range M, g i := by sorry
