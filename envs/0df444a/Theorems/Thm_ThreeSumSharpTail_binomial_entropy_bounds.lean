-- Prove2me | Theorems.Thm_ThreeSumSharpTail_binomial_entropy_bounds
-- name    : ThreeSumSharpTail.binomial_entropy_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:52:51.136992+00:00
-- url     : https://prove2.me/theorems/855a023f-a057-46c2-bfda-b79ac07eed11
-- title:
--   Two-sided binomial entropy bounds
-- statement:
--   For integers $r\ge1$ and $0\le k\le r$, let $p=k/r$. Then $$\frac{e^{rH(p)}}{r+1}\le\binom rk\le e^{rH(p)}.$$ The endpoints $k=0,r$ are included. This is a standard estimate used by the manuscript, not a novelty claim.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Lemma 3.1

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

theorem ThreeSumSharpTail.binomial_entropy_bounds (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r) :
    Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) / (r + 1) ≤ (Nat.choose r k : ℝ) ∧
    (Nat.choose r k : ℝ) ≤ Real.exp ((r : ℝ) * ThreeSumSharpTail.entropy ((k : ℝ) / r)) := by sorry
