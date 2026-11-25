-- Prove2me | Theorems.Thm_SNumbers_rank_quotient_inf_le
-- name    : SNumbers.rank_quotient_inf_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:24:43.483691+00:00
-- url     : https://prove2.me/theorems/879e266c-4d32-4346-8555-7b5f2bf23994
-- title:
--   SNumbers: rank quotient inf le
-- statement:
--   **Codimensions add up under intersections**:
--   `codim (M ⊓ N) ≤ codim M + codim N`. The map `x ↦ ([x]_M, [x]_N)` into
--   `X/M × X/N` has kernel `M ⊓ N`, so `X/(M ⊓ N)` is isomorphic to a subspace of
--   `X/M × X/N`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L260-L271
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L260-L271

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.rank_quotient_inf_le (M N : Submodule 𝕜 X) :
    Module.rank 𝕜 (X ⧸ (M ⊓ N)) ≤ Module.rank 𝕜 (X ⧸ M) + Module.rank 𝕜 (X ⧸ N) := by sorry
