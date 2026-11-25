-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_loc_piece
-- name    : ReciprocityTheory.L2DbarEstimates.F.loc_piece
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:02:38.33927+00:00
-- url     : https://prove2.me/theorems/074a6258-8343-5285-87e5-5826558da76a
-- title:
--   F: loc piece
-- statement:
--   The F construction uses the loc piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L324-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/LocalizeA.lean#L324-L489

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.loc_piece {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (hMD : MultDivStatement n M) (hMS : MultSStatement n M) (η : M → ℝ) (hη : SmoothR n z η)
    (hηc : HasCompactSupport η) (T : Set M) (hT : tsupport η ⊆ T)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : LocalL2Isometry (vol n z) G) (hD : LocalL2Isometry (vol n z) D) (hS : LocalL2Isometry (vol n z) S)
    (hGD : IsWeakDiv n z G D) (hGS : IsWeakS n z G S) :
    LocalL2Isometry (vol n z) (locG η G) ∧ LocalL2Isometry (vol n z) (locD n z η G D) ∧
      LocalL2Isometry (vol n z) (locS n z η G S) ∧
      IsWeakDiv n z (locG η G) (locD n z η G D) ∧ IsWeakS n z (locG η G) (locS n z η G S) ∧
      HasCompactSupport (locG η G) ∧ HasCompactSupport (locD n z η G D) ∧
      HasCompactSupport (locS n z η G S) ∧
      tsupport (locG η G) ⊆ T ∧ tsupport (locD n z η G D) ⊆ T ∧
      tsupport (locS n z η G S) ⊆ T := by sorry
