-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_eq_of_isMulLeftInvariant_of_univ
-- name    : PI.UnitaryGroupMassFormula.GelfConv.eq_of_isMulLeftInvariant_of_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:07.993895+00:00
-- url     : https://prove2.me/theorems/63c8692f-8cb0-467c-9687-093104f88fdb
-- title:
--   Gelf Conv: eq of is Mul Left Invariant of univ
-- statement:
--   The Gelf Conv construction uses the eq of is Mul Left Invariant of univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L12-L22

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

theorem PI.UnitaryGroupMassFormula.GelfConv.eq_of_isMulLeftInvariant_of_univ (μ ν : Measure G) [μ.IsHaarMeasure]
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (h : ν Set.univ = μ Set.univ) :
    ν = μ := by sorry
