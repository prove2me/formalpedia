-- Prove2me | Theorems.Thm_Supermultiplicative_exists_nonneg_not_tendsto_rpow_inv
-- name    : Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:28:11.993556+00:00
-- url     : https://prove2.me/theorems/c74c3f03-3fc9-5fda-b065-d345615f280b
-- title:
--   Supermultiplicative: exists nonneg not tendsto rpow inv
-- statement:
--   **Positivity is needed in `Supermultiplicative.tendsto_lim`.** Some nonnegative
--   supermultiplicative sequence `u` has no limit of `u n ^ (1 / n)`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/SupermultiplicativeCounterexample.lean#L69-L73
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/SupermultiplicativeCounterexample.lean#L69-L73

module
public import Definitions.Def_Fekete_Superadditive
public import Definitions.Def_Fekete_SupermultiplicativeCounterexample
set_option autoImplicit true
@[expose] public section
public section
open Filter Topology
open Supermultiplicative

theorem Supermultiplicative.exists_nonneg_not_tendsto_rpow_inv :
    ∃ u : ℕ → ℝ, (∀ n, 0 ≤ u n) ∧ Supermultiplicative u ∧
      ¬ ∃ L, Tendsto (fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) atTop (𝓝 L) := by sorry
