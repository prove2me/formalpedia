-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_test
-- name    : ReciprocityTheory.L2DbarEstimates.F.chT_test
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:00.095593+00:00
-- url     : https://prove2.me/theorems/eefc6fef-b2ad-42b6-bdd0-cdab9779ca4f
-- title:
--   F: ch T test
-- statement:
--   The F construction uses the ch T test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ChartA.lean#L115-L127

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem ReciprocityTheory.L2DbarEstimates.F.chT_test (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (ψ : V n → ℂ) (hψd : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ e.target) :
    IsTest n z (e.source.indicator (ψ ∘ e)) ∧
    (∀ y ∈ e.target, e.source.indicator (ψ ∘ e) (e.symm y) = ψ y) ∧
    (∀ j, ∀ y ∈ e.target, d n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wd n j ψ y ∧
        db n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wdb n j ψ y) := by sorry
