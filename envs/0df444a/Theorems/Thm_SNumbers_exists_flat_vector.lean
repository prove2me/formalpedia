-- Prove2me | Theorems.Thm_SNumbers_exists_flat_vector
-- name    : SNumbers.exists_flat_vector
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:51:31.978944+00:00
-- url     : https://prove2.me/theorems/4bae0015-8e6e-539d-a449-a8ac48c7eb24
-- title:
--   SNumbers: exists flat vector
-- statement:
--   **Flatness lemma.** A subspace `V ⊆ 𝕜^m` of dimension `≥ k ≥ 1` contains a
--   nonzero vector `x` with `‖x i‖ ≤ 1` everywhere and `‖x i‖ = 1` on at least `k`
--   coordinates.
--
--   This is the unit-weight case `w ≡ 1` of `exists_flat_vector_weighted`; the
--   hypothesis `1 ≤ k` additionally forces `x ≠ 0`, since at least one coordinate
--   has `‖x i‖ = 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L191-L205
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L191-L205

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

theorem SNumbers.exists_flat_vector {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (hk : 1 ≤ k) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ (∀ i, ‖x i‖ ≤ 1) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = 1)).card := by sorry
