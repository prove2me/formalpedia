-- Prove2me | Theorems.Thm_SCCThm8_power_rigidity
-- name    : SCCThm8.power_rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:46.498875+00:00
-- url     : https://prove2.me/theorems/28c6c94e-3316-41a8-9d14-27587b04fae8
-- title:
--   SCCThm8: power rigidity
-- statement:
--   **Block rigidity for `T_k^{⊗m}`.** Let `k ≥ 2`, and index the tensor power by `m`-tuples of
--   `k`-subsets of `Fin (3k)`. Suppose `f₁ A * f₂ B * f₃ C = 1` whenever `A j, B j, C j` are pairwise
--   disjoint in every block `j`. Then there are pairwise commuting `g j i` (over all blocks and points)
--   such that for every triple of tuples, `f₁ A * f₂ B * f₃ C = ∏_j ∏_i (g j i)^(multP A B C j i - 1)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L291-L350
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L291-L350

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset

theorem SCCThm8.power_rigidity {G : Type*} [Group G] (k m : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G)
    (hP : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
      f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin m → Fin (3 * k) → G, (∀ j i j' i', Commute (g j i) (g j' i')) ∧
      ∀ A B C : Fin m → Finset (Fin (3 * k)),
        (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
        f₁ A * f₂ B * f₃ C = psiP g (fun j i => multP A B C j i - 1) := by sorry
