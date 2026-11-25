-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_NCA_map_eq_of_split
-- name    : PI.LevelKSplit.W.NCA.map_eq_of_split
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:54.998812+00:00
-- url     : https://prove2.me/theorems/39e68066-ef50-4d0e-993a-b6e5fee942a5
-- title:
--   NCA: map eq of split
-- statement:
--   The NCA construction uses the map eq of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmV.lean#L18-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/NCAsmV.lean#L18-L113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
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
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem PI.LevelKSplit.W.NCA.map_eq_of_split (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by sorry
