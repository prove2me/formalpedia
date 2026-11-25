-- Prove2me | Theorems.Thm_ShannonCapacity_indepNum_le
-- name    : ShannonCapacity.indepNum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:26.822635+00:00
-- url     : https://prove2.me/theorems/f30d2c6f-fb1b-42ef-9f19-e95ad00e203e
-- title:
--   Shannon Capacity: indep Num le
-- statement:
--   **Lovász (1979).** An orthonormal representation with handle `c` bounds the independence
--   number.
--
--   Source: https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L46-L50
-- source:
--   https://github.com/jtraverso/lovasz-theta/blob/2d506b5abca378d9133b5e3f1264a5316843c9a7/Solution.lean#L46-L50

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Definitions.Def_LovaszTheta_Solution
public import Theorems.Thm_LovaszTheta_indepNum_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ShannonCapacity
variable {V : Type*}

theorem ShannonCapacity.indepNum_le [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) :
    (G.indepNum : ℝ) ≤ t := by sorry
