-- Prove2me | Theorems.Thm_SCCThm8_Rig_dl_spec
-- name    : SCCThm8.Rig.dl_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:19.244428+00:00
-- url     : https://prove2.me/theorems/628311ca-df2f-49c3-b160-f3b395edfbc7
-- title:
--   Rig: dl spec
-- statement:
--   The Rig construction uses the dl spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L119-L128
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L119-L128

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
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}

theorem SCCThm8.Rig.dl_spec (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    (A : Finset (Fin (3 * k))) (hA : A.card = k) (i j : Fin (3 * k)) (hi : i ∈ A) (hj : j ∉ A) :
    f₁ (sw A i j) = dl k f₁ i j * f₁ A := by sorry
