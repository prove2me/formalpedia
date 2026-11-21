-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequence_weighted_l1_map
-- name    : RiemannMasullo.rapidDecaySequence_weighted_l1_map
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:51:05.312934+00:00
-- url     : https://prove2.me/theorems/7fb4a635-58d0-486a-8932-d58c0062bc8a
-- title:
--   Weighted coordinate maps realize the rapid-decay seminorms as ℓ¹ norms
-- statement:
--   For every order j, multiplication by (1+‖a‖)^j defines a continuous linear map from rapidly decreasing sequences to ℓ¹. The ℓ¹ norm of the image equals the j-th defining seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L574-L588

import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Mathlib
open RiemannMasullo
open scoped ENNReal

namespace RiemannMasullo
theorem rapidDecaySequence_weighted_l1_map (r j : ℕ) :
    let W := fun a : Fin r → ℤ =>
      (1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖)^j
    ∃ L : RapidDecaySequence r →L[ℂ] lp (fun _ : Fin r → ℤ => ℂ) 1,
      (∀ s a, L s a = (W a : ℂ)*s a) ∧ ∀ s, ‖L s‖ = rapidDecaySequenceSeminorm j s := by sorry
end RiemannMasullo
