-- Prove2me | Theorems.Thm_ThreeSum_Coloring_two_coordinates_separate
-- name    : ThreeSum.Coloring.two_coordinates_separate
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:38:41.381985+00:00
-- url     : https://prove2.me/theorems/44480efe-b709-4747-a1a4-7f2841142723
-- title:
--   Two coordinates distinguish three binary words
-- statement:
--   Let $\alpha$ be any coordinate type, and let $s,t,u:\alpha\to\{0,1\}$ be three pairwise distinct binary words. There exist coordinates $i,j\in\alpha$ for which their two-coordinate restrictions are pairwise distinct:
--
--   $$
--   (s_i,s_j)\ne(t_i,t_j),\qquad (s_i,s_j)\ne(u_i,u_j),\qquad (t_i,t_j)\ne(u_i,u_j).
--   $$
--
--   No finiteness assumption on $\alpha$ is needed. This separation fact supplies the small family of coordinate projections used in the deterministic three-color reduction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/Coloring.lean#L34-L54

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1

theorem ThreeSum.Coloring.two_coordinates_separate : ∀ {α : Type u_1} {s t u : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t) (hsu : @Ne.{u_1 + 1} (α → Bool) s u)
  (htu : @Ne.{u_1 + 1} (α → Bool) t u),
  ∃ (i : α) (j : α),
    And
      (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j)) (@Prod.mk.{0, 0} Bool Bool (t i) (t j)))
      (And
        (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (s i) (s j))
          (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))
        (@Ne.{1} (Prod.{0, 0} Bool Bool) (@Prod.mk.{0, 0} Bool Bool (t i) (t j))
          (@Prod.mk.{0, 0} Bool Bool (u i) (u j)))) := by
  sorry
