-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_MapPiScale_map_pi_scale
-- name    : UpperTheory.Reformulated.B.MapPiScale.map_pi_scale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:48.89185+00:00
-- url     : https://prove2.me/theorems/c1e8e47e-af20-48e1-9f45-9c76380a5889
-- title:
--   Map Pi Scale: map pi scale
-- statement:
--   The Map Pi Scale construction uses the map pi scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapPiScale.lean#L4-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapPiScale.lean#L4-L22

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapPiScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory

theorem UpperTheory.Reformulated.B.MapPiScale.map_pi_scale :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by sorry
