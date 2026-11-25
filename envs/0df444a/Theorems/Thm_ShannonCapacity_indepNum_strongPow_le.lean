-- Prove2me | Theorems.Thm_ShannonCapacity_indepNum_strongPow_le
-- name    : ShannonCapacity.indepNum_strongPow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:44.928154+00:00
-- url     : https://prove2.me/theorems/b2be9dda-384e-4af3-ac32-3eaf9c7718eb
-- title:
--   Shannon Capacity: indep Num strong Pow le
-- statement:
--   **Lovász (1979), multiplicativity.** The same bound holds for strong powers, with `t^k`.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L53-L57
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L53-L57

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_strongPow_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}

theorem ShannonCapacity.indepNum_strongPow_le [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) (k : ℕ) :
    ((strongPow G k).indepNum : ℝ) ≤ t ^ k := by sorry
