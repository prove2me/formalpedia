-- Prove2me | Theorems.Thm_SNumbers_exists_flat_vector_weighted
-- name    : SNumbers.exists_flat_vector_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:26.642623+00:00
-- url     : https://prove2.me/theorems/42689e95-9272-5ad2-bec2-665bf4f038e1
-- title:
--   SNumbers: exists flat vector weighted
-- statement:
--   **Weighted flatness lemma.** For a nonnegative weight `w`, a subspace
--   `V ⊆ 𝕜^m` of dimension `≥ k` contains a vector `x` with `‖x i‖ ≤ w i`
--   everywhere that **saturates** the weight (`‖x i‖ = w i`) on at least `k`
--   coordinates. An extreme point `x` of the compact set
--   `B = {x ∈ V : ∀ i, ‖x i‖ ≤ w i}` (Krein–Milman) must saturate `≥ dim V`
--   coordinates: otherwise the coordinate-pigeonhole vector `y` vanishing on the
--   saturated set `S` makes `x` the midpoint of a nondegenerate segment
--   `x ± ε·y ⊆ B`, contradicting extremality. (Nonvanishing of `x` is not asserted
--   here; for the unweighted case it is recovered in `exists_flat_vector`.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L104-L182
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/FlatnessLemmas.lean#L104-L182

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

theorem SNumbers.exists_flat_vector_weighted {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, (∀ i, ‖x i‖ ≤ w i) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = w i)).card := by sorry
