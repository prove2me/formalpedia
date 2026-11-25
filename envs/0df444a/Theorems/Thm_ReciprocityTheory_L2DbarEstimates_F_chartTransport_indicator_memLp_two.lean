-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chartTransport_indicator_memLp_two
-- name    : ReciprocityTheory.L2DbarEstimates.F.chartTransport_indicator_memLp_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:51.377814+00:00
-- url     : https://prove2.me/theorems/97a21064-56bf-463c-8867-224cc5894ace
-- title:
--   F: chart Transport indicator mem Lp two
-- statement:
--   The F construction uses the chart Transport indicator mem Lp two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L45-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L45-L68

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem ReciprocityTheory.L2DbarEstimates.F.chartTransport_indicator_memLp_two {E : Type*} [NormedAddCommGroup E] [T2Space M] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : LocalL2Isometry (vol n z) f) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ e.source) :
    MemLp (e.target.indicator (f ∘ e.symm)) 2 volume := by sorry
