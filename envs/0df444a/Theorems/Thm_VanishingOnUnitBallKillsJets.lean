-- Prove2me | Theorems.Thm_VanishingOnUnitBallKillsJets
-- name    : VanishingOnUnitBallKillsJets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:56.626181+00:00
-- url     : https://prove2.me/theorems/5a5d7530-05de-4970-8650-ec4aeed40830
-- title:
--   Vanishing On Unit Ball Kills Jets: Vanishing On Unit Ball Kills Jets
-- statement:
--   A smooth function on the plane that vanishes on the closed unit ball has all of its
--   DIAGONAL jets at the origin equal to zero, in every direction and at every order.
--
--   This is the definiteness half of the sup-norm argument in `PolyInverseEstimate`: there the
--   hypothesis arrives as `N(S) = 0`, which says exactly that `S` vanishes on the closed unit ball,
--   and what is needed is the vanishing of the diagonal evaluations so that the rigidity statement
--   applies.
--
--   The route is NOT the one-line appeal to locality of `D^j` that it looks like.  The `.tex` records
--   why: the development's background has no clause making `D^j` local on the plane, nor one saying
--   that a function vanishing on an open subset has vanishing `D^j` there.  What it does have is
--   locality in ONE variable, so the proof restricts `S` to the ray `s |-> s w`, uses one-variable
--   locality on `(-1,1)`, and transfers back with `IteratedDerivAlongRay`.  That route reaches only
--   directions `w` in the closed unit ball, which is why the last step removes the restriction by
--   positive homogeneity of a diagonal evaluation.  The Lean follows the same route for that reason,
--   although Mathlib would supply the multivariable locality directly.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/VanishingOnUnitBallKillsJets.lean#L19-L65
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/VanishingOnUnitBallKillsJets.lean#L19-L65

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_VanishingOnUnitBallKillsJets
import Theorems.Thm_IteratedDerivAlongRay

set_option autoImplicit false

theorem VanishingOnUnitBallKillsJets (S : Plane → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (hvan : ∀ w : Plane, ‖w‖ ≤ 1 → S w = 0) :
    ∀ (j : ℕ) (w : Plane), iteratedFDeriv ℝ j S 0 (fun _ => w) = 0 := by sorry
