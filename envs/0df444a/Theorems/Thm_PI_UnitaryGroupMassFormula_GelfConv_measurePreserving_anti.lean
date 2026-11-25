-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_measurePreserving_anti
-- name    : PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_anti
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:52.449589+00:00
-- url     : https://prove2.me/theorems/52fb7c76-786b-47df-b6d7-f6433b17c21e
-- title:
--   Gelf Conv: measure Preserving anti
-- statement:
--   The Gelf Conv construction uses the measure Preserving anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L47-L67

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

theorem PI.UnitaryGroupMassFormula.GelfConv.measurePreserving_anti (μ : Measure G) [μ.IsHaarMeasure] (τ : G → G) (hc : Continuous τ)
    (hm : ∀ x y, τ (x * y) = τ y * τ x) (hi : ∀ x, τ (τ x) = x) :
    MeasurePreserving τ μ μ := by sorry
