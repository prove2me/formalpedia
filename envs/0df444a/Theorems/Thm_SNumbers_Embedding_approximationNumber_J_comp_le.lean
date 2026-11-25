-- Prove2me | Theorems.Thm_SNumbers_Embedding_approximationNumber_J_comp_le
-- name    : SNumbers.Embedding.approximationNumber_J_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:42.06405+00:00
-- url     : https://prove2.me/theorems/b546ce91-ac7f-4951-ad48-0da9a3c0b6c0
-- title:
--   Embedding: approximation Number J comp le
-- statement:
--   The approximation numbers of `J_Y ∘ S` are at most the Gelfand numbers of `S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L194-L201
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L194-L201

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

theorem SNumbers.Embedding.approximationNumber_J_comp_le (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber ((J : Y →L[𝕜] _).comp S) n ≤ gelfandNumber S n := by sorry
