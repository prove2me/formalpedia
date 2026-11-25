-- Prove2me | Theorems.Thm_SNumbers_sn_comp_metricInjection_le
-- name    : SNumbers.sn_comp_metricInjection_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:50.023985+00:00
-- url     : https://prove2.me/theorems/601ae0c1-5694-5bca-a407-5fd7e076553a
-- title:
--   SNumbers: sn comp metric Injection le
-- statement:
--   For every `s`-number sequence, `sₙ(J ∘ S) ≤ sₙ(S)` when `J` is a metric
--   injection. (Just the (S3) ideal property with `‖J‖ ≤ 1`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L167-L177
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L167-L177

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.sn_comp_metricInjection_le {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) (n : ℕ) :
    s (J.comp S) n ≤ s S n := by sorry
