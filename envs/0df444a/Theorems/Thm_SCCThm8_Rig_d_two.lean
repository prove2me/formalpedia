-- Prove2me | Theorems.Thm_SCCThm8_Rig_d_two
-- name    : SCCThm8.Rig.d_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:40.681547+00:00
-- url     : https://prove2.me/theorems/c8d8726b-3b48-5f25-a7e8-f771a2910214
-- title:
--   Rig: d two
-- statement:
--   Step 5: two-swap.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L196-L206
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L196-L206

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

theorem SCCThm8.Rig.d_two {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    d i' j' * d i j = d i' j * d i j' := by sorry
