-- Prove2me | Theorems.Thm_SNumbers_rank_id_piLp
-- name    : SNumbers.rank_id_piLp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:31.744605+00:00
-- url     : https://prove2.me/theorems/68dd2199-f7cd-4d5a-9370-3001c1909e40
-- title:
--   SNumbers: rank id pi Lp
-- statement:
--   The rank of the identity on `ℓ^p_k` is `k` (as a `Cardinal`). Used to bound
--   the rank of finite-rank approximants that factor through `ℓ^p_k`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L62-L69
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L62-L69

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SNumbers.rank_id_piLp (k : ℕ) :
    (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin k => 𝕜))).rank = (k : Cardinal) := by sorry
