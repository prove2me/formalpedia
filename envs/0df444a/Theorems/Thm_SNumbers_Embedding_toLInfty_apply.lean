-- Prove2me | Theorems.Thm_SNumbers_Embedding_toLInfty_apply
-- name    : SNumbers.Embedding.toLInfty_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:05.523703+00:00
-- url     : https://prove2.me/theorems/24cc7ae2-a4c3-4737-86d4-249c05d0342f
-- title:
--   Embedding: to LInfty apply
-- statement:
--   The Embedding construction uses the to LInfty apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L97-L99
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L97-L99

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
variable {ι : Type u}

theorem SNumbers.Embedding.toLInfty_apply (f : ι → X →L[𝕜] 𝕜) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖f i‖ ≤ C) (x : X) (i : ι) :
    (toLInfty f hC0 hC x : ι → 𝕜) i = f i x := by sorry

attribute [defeq] SNumbers.Embedding.toLInfty_apply
