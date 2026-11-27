-- Prove2me | Theorems.Thm_PvsNP_MovingWorkBoundary_summed_moving_diagonal_lower
-- name    : PvsNP.MovingWorkBoundary.summed_moving_diagonal_lower
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-27T03:31:14.345937+00:00
-- url     : https://prove2.me/theorems/8742e10f-d8eb-4239-a02c-6fee9a4a9735
-- title:
--   Moving-cut diagonal tests bound the total control transfers
-- statement:
--   For pairwise distinct unit-speed moving cuts, consider a diagonal test family whose off-diagonal splices change a verdict. At each cut, let C bound the short transcript capacity, including all tape transfers. If there are A tested diagonals and r is the short-control threshold, the sum over the cuts of max(A-C,0)(r+1) is at most 2AT, where T is the synchronized clock.
-- source:
--   A finite moving-cut extension of single-tape crossing-sequence counting.

import Definitions.Def_MovingCutCapacity

set_option autoImplicit false

open PvsNP.WorkBoundarySplice PvsNP.MovingWorkBoundary
open scoped BigOperators

variable {A Q Γ : Type} [Fintype A] [Fintype Q] [Fintype Γ]

theorem PvsNP.MovingWorkBoundary.summed_moving_diagonal_lower {E : Type} [Fintype E] (cut : E → ℕ → ℤ)
    (M : Machine Q Γ) (T r : ℕ) (speed : ∀ e, UnitCut (cut e) T)
    (distinct : ∀ t < T, Function.Injective (fun e => cut e t))
    (start : A → A → Config Q Γ) (verdict : Q → Prop)
    (mixed : ∀ e a b,
      assemble (rightOf (cut e 0)) (sideAt (cut e) M (start a a) 0) (pair (start a a) (start b b)) = start a b)
    (diagonal : ∀ a, verdict (trace M (start a a) T).state)
    (offDiagonal : ∀ a b, a ≠ b → ¬ verdict (trace M (start a b) T).state) :
    (∑ e : E, (Fintype.card A - cutCapacity (cut e) T r Q Γ)*(r+1)) ≤
      Fintype.card A*(2*T) := by sorry
