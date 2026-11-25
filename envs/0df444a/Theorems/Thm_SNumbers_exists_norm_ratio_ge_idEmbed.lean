-- Prove2me | Theorems.Thm_SNumbers_exists_norm_ratio_ge_idEmbed
-- name    : SNumbers.exists_norm_ratio_ge_idEmbed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:03.232701+00:00
-- url     : https://prove2.me/theorems/e0b416aa-bec3-4cc8-a144-5fab1823991a
-- title:
--   SNumbers: exists norm ratio ge id Embed
-- statement:
--   **Geometric input.** Every subspace `V ⊆ ℓ^q_m` of dimension `≥ m - n`
--   contains a nonzero `x` with `(m-n)^{1/p-1/q} · ‖x‖_q ≤ ‖x‖_p` (`= ‖id x‖`).
--   The classical Gelfand-width lower bound (Pietsch §11.11).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L292-L306
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/Identity.lean#L292-L306

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}

theorem SNumbers.exists_norm_ratio_ge_idEmbed {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m)
    (V : Submodule 𝕜 (PiLp q (fun _ : Fin m => 𝕜))) (hV : m - n ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) * ‖x‖
      ≤ ‖idEmbed (𝕜 := 𝕜) (m := m) p q x‖ := by sorry
