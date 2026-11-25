-- Prove2me | Theorems.Thm_SNumbers_Embedding_isMetricInjection_J
-- name    : SNumbers.Embedding.isMetricInjection_J
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:06.569068+00:00
-- url     : https://prove2.me/theorems/41244678-5d4b-4497-99fb-e35805028fdd
-- title:
--   Embedding: is Metric Injection J
-- statement:
--   **`J_Y` is a metric injection**: `‖J_Y y‖ = ‖y‖`, the upper bound because every
--   coordinate is a functional of norm at most `1`, the lower bound by a norming functional
--   (Hahn–Banach).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L122-L134
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L122-L134

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_GelfandEmbedding
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
open SNumbers.Embedding
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.Embedding.isMetricInjection_J : IsMetricInjection (J : Y →L[𝕜] _) := by sorry
