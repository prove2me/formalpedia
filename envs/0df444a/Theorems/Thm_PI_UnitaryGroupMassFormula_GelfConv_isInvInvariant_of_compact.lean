-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_isInvInvariant_of_compact
-- name    : PI.UnitaryGroupMassFormula.GelfConv.isInvInvariant_of_compact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:58.16523+00:00
-- url     : https://prove2.me/theorems/5380ed0a-16a9-4914-b578-c28e33aebbbb
-- title:
--   Gelf Conv: is Inv Invariant of compact
-- statement:
--   The Gelf Conv construction uses the is Inv Invariant of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L29-L32

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

theorem PI.UnitaryGroupMassFormula.GelfConv.isInvInvariant_of_compact (μ : Measure G) [μ.IsHaarMeasure] : μ.IsInvInvariant := by sorry
