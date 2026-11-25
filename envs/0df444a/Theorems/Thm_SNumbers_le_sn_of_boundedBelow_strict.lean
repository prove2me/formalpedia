-- Prove2me | Theorems.Thm_SNumbers_le_sn_of_boundedBelow_strict
-- name    : SNumbers.le_sn_of_boundedBelow_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:12.565213+00:00
-- url     : https://prove2.me/theorems/2b419e05-794a-463b-98dc-1dcda8848d71
-- title:
--   SNumbers: le sn of bounded Below strict
-- statement:
--   **Core lower bound.** If `f : E →L[𝕜] F` is bounded below by `c > 0` on a
--   space `E` with `n < dim E`, then every injective strict `s`-number sequence `s`
--   satisfies `c ≤ sₙ(f)`.
--
--   This isolates the heart of the extremality theorem: `f` is corestricted to its
--   range `V` (an isometric copy inside `F`), where it is a continuous linear
--   isomorphism `f₀` with `‖f₀⁻¹‖ ≤ 1/c`. Injectivity of `s` removes the inclusion
--   `V ↪ F`, and the ideal property plus strict normalisation `sₙ(id_E) = 1` give the
--   bound.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L515-L583
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L515-L583

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
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

theorem SNumbers.le_sn_of_boundedBelow_strict {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (hE : n < Module.finrank 𝕜 E) {c : ℝ} (hc : 0 < c)
    (f : E →L[𝕜] F) (hf : ∀ x, c * ‖x‖ ≤ ‖f x‖) :
    c ≤ s f n := by sorry
