-- Prove2me | Theorems.Thm_SCCThm8_Rig_d_inv
-- name    : SCCThm8.Rig.d_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:02.717828+00:00
-- url     : https://prove2.me/theorems/7f59f4b1-ac9d-5e9f-bb67-76120e31df6a
-- title:
--   Rig: d inv
-- statement:
--   Step 3.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L178-L184
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L178-L184

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

theorem SCCThm8.Rig.d_inv {i j : Fin (3 * k)} (hij : i ≠ j) : d j i * d i j = 1 := by sorry
