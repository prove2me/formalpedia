-- Prove2me | Theorems.Thm_SNumbers_sn_comp_metricSurjection_le
-- name    : SNumbers.sn_comp_metricSurjection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:02:10.119932+00:00
-- url     : https://prove2.me/theorems/ec872347-e104-45e5-8cb7-cd322f72066f
-- title:
--   SNumbers: sn comp metric Surjection le
-- statement:
--   For every `s`-number sequence, `sₙ(S ∘ Q) ≤ sₙ(S)` when `Q` is a metric
--   surjection. (Just the (S3) ideal property with `‖Q‖ ≤ 1`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L181-L193
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L181-L193

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

theorem SNumbers.sn_comp_metricSurjection_le {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q) (n : ℕ) :
    s (S.comp Q) n ≤ s S n := by sorry
