-- Prove2me | Theorems.Thm_ThreeSumSharpTail_threeSum_1999017
-- name    : ThreeSumSharpTail.threeSum_1999017
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:55:00.436813+00:00
-- url     : https://prove2.me/theorems/1674355a-fcd8-4885-8ec3-cc3e1ff29624
-- title:
--   Deterministic integer 3SUM in O(n^1.999017) word-RAM steps
-- statement:
--   For each fixed $\kappa\in\mathbb N$, there exist a finite deterministic word-RAM program $P$, a natural number $b$, and a step bound $T:\mathbb N\to\mathbb N$. For every $n$, input $x:\{0,\ldots,n-1\}\to\mathbb Z$ with $|x_i|\le n^\kappa$, and every $W\ge b(\operatorname{Nat.log2}(n)+1)$, the program halts within $T(n)$ steps and accepts exactly when three pairwise distinct indices have sum zero. Equal values at distinct indices are allowed; no witness is required; inputs of size less than three are rejected.
--
--   The exact time requirement is $\exists K\in\mathbb N\;\forall n\ge2,\ T(n)^{1000000}\le K n^{1999017}$, equivalent to $T(n)=O(n^{1.999017})$. The target instantiates the campaign template without changing its definitions.
--
--   Source: Theorem 1.1 of Xu's sharp-tail manuscript. The manuscript states $\kappa\ge1$ and a sufficiently large logarithmic word width; the campaign additionally makes uniformity over all larger widths explicit. The case $\kappa=0$ follows from the $\kappa=1$ bound for $n\ge1$, with $n=0$ handled separately. The formal development must justify this interface adaptation. The improved bound is a proposed formalization target, not an already Lean-certified result.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Theorem 1.1; shared campaign interface adaptation

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem ThreeSumSharpTail.threeSum_1999017 :
    EndStatement.ThreeSum.SolvedInTime 1.999017 := by sorry
