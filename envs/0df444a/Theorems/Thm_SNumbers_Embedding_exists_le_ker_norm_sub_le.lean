-- Prove2me | Theorems.Thm_SNumbers_Embedding_exists_le_ker_norm_sub_le
-- name    : SNumbers.Embedding.exists_le_ker_norm_sub_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:26:39.449322+00:00
-- url     : https://prove2.me/theorems/978e4e1b-c147-4e37-a746-db32f3a1cdf1
-- title:
--   Embedding: exists le ker norm sub le
-- statement:
--   **Hahn–Banach approximant.** For a subspace `M` of `X` there is a continuous linear
--   map `L : X → ℓ_∞(B_{Y*})` vanishing on `M` with `‖J_Y ∘ S - L‖ ≤ ‖S|_M‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L148-L189
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/GelfandEmbedding.lean#L148-L189

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

theorem SNumbers.Embedding.exists_le_ker_norm_sub_le (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    ∃ L : X →L[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞,
      M ≤ LinearMap.ker (L : X →ₗ[𝕜] lp (fun _ : DualBall 𝕜 Y => 𝕜) ∞) ∧
        ‖(J : Y →L[𝕜] _).comp S - L‖ ≤ ‖S.comp M.subtypeL‖ := by sorry
