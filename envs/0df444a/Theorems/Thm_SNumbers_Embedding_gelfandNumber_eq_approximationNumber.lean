-- Prove2me | Theorems.Thm_SNumbers_Embedding_gelfandNumber_eq_approximationNumber
-- name    : SNumbers.Embedding.gelfandNumber_eq_approximationNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:14:56.493147+00:00
-- url     : https://prove2.me/theorems/cd9679c2-ade0-4f2f-88d1-a08c802e218e
-- title:
--   Embedding: gelfand Number eq approximation Number
-- statement:
--   **Pietsch's embedding identity** `cₙ(S) = aₙ(J_Y ∘ S)`: the Gelfand numbers are the
--   approximation numbers after the canonical embedding of the codomain into `ℓ_∞(B_{Y*})`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L205-L209
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L205-L209

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

theorem SNumbers.Embedding.gelfandNumber_eq_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n = approximationNumber ((J : Y →L[𝕜] _).comp S) n := by sorry
