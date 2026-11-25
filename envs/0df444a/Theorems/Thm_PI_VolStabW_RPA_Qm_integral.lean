-- Prove2me | Theorems.Thm_PI_VolStabW_RPA_Qm_integral
-- name    : PI.VolStabW.RPA.Qm_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:14.063948+00:00
-- url     : https://prove2.me/theorems/07c700b4-a3a9-43af-8c0d-3e4a2ef26002
-- title:
--   RPA: Qm integral
-- statement:
--   The RPA construction uses the Qm integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/KapIntegral.lean#L16-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/KapIntegral.lean#L16-L76

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

theorem PI.VolStabW.RPA.Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by sorry
