-- Prove2me | Theorems.Thm_SCCThm8_Rig_d_cocycle
-- name    : SCCThm8.Rig.d_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:11.810213+00:00
-- url     : https://prove2.me/theorems/c4f2df08-dc5c-539c-b9be-9187e301749c
-- title:
--   Rig: d cocycle
-- statement:
--   Step 4: cocycle.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L187-L193
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L187-L193

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

theorem SCCThm8.Rig.d_cocycle {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    d i l = d j l * d i j := by sorry
