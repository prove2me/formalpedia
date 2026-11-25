-- Prove2me | Theorems.Thm_SNumbers_Embedding_rank_le_rank_quotient_of_le_ker
-- name    : SNumbers.Embedding.rank_le_rank_quotient_of_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:26:10.51393+00:00
-- url     : https://prove2.me/theorems/c9ccd11b-1c91-4876-a7ae-1c3e95edf10a
-- title:
--   Embedding: rank le rank quotient of le ker
-- statement:
--   A continuous linear map that vanishes on `M` has rank at most `codim M`: it factors
--   through `X ⧸ M`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L140-L144
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L140-L144

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

theorem SNumbers.Embedding.rank_le_rank_quotient_of_le_ker {Z : Type u} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (L : X →L[𝕜] Z) {M : Submodule 𝕜 X} (h : M ≤ LinearMap.ker (L : X →ₗ[𝕜] Z)) :
    L.rank ≤ Module.rank 𝕜 (X ⧸ M) := by sorry
