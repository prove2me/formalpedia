-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_GelfConv_integral_comp_homeo
-- name    : PI.UnitaryGroupMassFormula.GelfConv.integral_comp_homeo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:51.317697+00:00
-- url     : https://prove2.me/theorems/64dbb647-1222-4035-9f9d-4a5622647b46
-- title:
--   Gelf Conv: integral comp homeo
-- statement:
--   The Gelf Conv construction uses the integral comp homeo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandPairConvolution/Unimod.lean#L69-L72

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

theorem PI.UnitaryGroupMassFormula.GelfConv.integral_comp_homeo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) (e : G ≃ₜ G) (he : MeasurePreserving e μ μ) (f : G → E) :
    ∫ x, f (e x) ∂μ = ∫ x, f x ∂μ := by sorry
