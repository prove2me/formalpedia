-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCA_conjInv_of_one
-- name    : PI.LevelKSplit.W.NCA.conjInv_of_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:43.017432+00:00
-- url     : https://prove2.me/theorems/41924749-5a0e-470f-a57a-f498ee986a88
-- title:
--   NCA: conj Inv of one
-- statement:
--   The NCA construction uses the conj Inv of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmM.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmM.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem PI.LevelKSplit.W.NCA.conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by sorry
