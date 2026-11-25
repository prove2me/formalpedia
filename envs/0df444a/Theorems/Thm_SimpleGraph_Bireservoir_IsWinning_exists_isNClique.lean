-- Prove2me | Theorems.Thm_SimpleGraph_Bireservoir_IsWinning_exists_isNClique
-- name    : SimpleGraph.Bireservoir.IsWinning.exists_isNClique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:21.825943+00:00
-- url     : https://prove2.me/theorems/706f4a63-d544-5f7b-835e-4a349dc8c9f9
-- title:
--   Is Winning: exists is NClique
-- statement:
--   **Winning states win.** Following winning pivots from a winning state reaches a red `K_r` or a
--   blue `K_s`.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L275-L292
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Bireservoir.lean#L275-L292

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
variable {S}

theorem SimpleGraph.Bireservoir.IsWinning.exists_isNClique {R : ℕ → ℕ → ℕ} {r s : ℕ} (hR : IsPascal R)
    (hS : S.IsWinning R r s) : (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by sorry
