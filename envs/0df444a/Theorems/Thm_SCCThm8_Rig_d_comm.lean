-- Prove2me | Theorems.Thm_SCCThm8_Rig_d_comm
-- name    : SCCThm8.Rig.d_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:42.311947+00:00
-- url     : https://prove2.me/theorems/2c3b155c-036d-539f-b078-f477ec49ffb0
-- title:
--   Rig: d comm
-- statement:
--   Step 6: shared-index commutation.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L209-L226
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L209-L226

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}
variable (hk : 2 ≤ k)
  (hs : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = d i j * F A)
include hk hs

theorem SCCThm8.Rig.d_comm {a b c : Fin (3 * k)} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Commute (d a b) (d b c) := by sorry
