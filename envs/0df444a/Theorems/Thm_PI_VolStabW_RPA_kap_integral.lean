-- Prove2me | Theorems.Thm_PI_VolStabW_RPA_kap_integral
-- name    : PI.VolStabW.RPA.kap_integral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:40:07.12877+00:00
-- url     : https://prove2.me/theorems/e7a24c1f-c16b-4fe0-97bc-15f9b86bdcfc
-- title:
--   RPA: kap integral
-- statement:
--   The RPA construction uses the kap integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/KapIntegral.lean#L78-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/KapIntegral.lean#L78-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_ESSymmApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_KapIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RPA
open MeasureTheory Filter Finset
open scoped NNReal ENNReal
variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

theorem PI.VolStabW.RPA.kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by sorry
