-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_of_hom
-- name    : PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_of_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:03.376352+00:00
-- url     : https://prove2.me/theorems/c9a609a0-4b5d-4a76-b29a-725293678a45
-- title:
--   Gelf Conv: measure Preserving of hom
-- statement:
--   The Gelf Conv construction uses the measure Preserving of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L34-L36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandPairConvolution_Unimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfConv
open MeasureTheory Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_of_hom (μ : Measure G) [μ.IsHaarMeasure] (σ : G →* G)
    (hc : Continuous σ) (hs : Function.Surjective σ) : MeasurePreserving σ μ μ := by sorry
