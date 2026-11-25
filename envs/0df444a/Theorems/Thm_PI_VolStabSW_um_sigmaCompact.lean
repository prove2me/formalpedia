-- Prove2me | Theorems.Thm_PI_VolStabSW_um_sigmaCompact
-- name    : PI.VolStabSW.um_sigmaCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:14.508876+00:00
-- url     : https://prove2.me/theorems/22e76a86-a2b9-4a8a-92ed-b56032c6451f
-- title:
--   Vol Stab SW: um sigma Compact
-- statement:
--   The Vol Stab SW construction uses the um sigma Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/Unimod.lean#L75-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/Unimod.lean#L75-L139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem PI.VolStabSW.um_sigmaCompact (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : SigmaCompactSpace G := by sorry
