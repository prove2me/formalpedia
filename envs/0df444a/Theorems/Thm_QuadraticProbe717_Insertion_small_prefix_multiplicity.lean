-- Prove2me | Theorems.Thm_QuadraticProbe717_Insertion_small_prefix_multiplicity
-- name    : QuadraticProbe717.Insertion.small_prefix_multiplicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:35.915419+00:00
-- url     : https://prove2.me/theorems/4558a13d-43d4-4860-b41d-d6834a00094d
-- title:
--   Section 6.1 — subpolynomial maximal divisor bound
-- statement:
--   For every $\eta>0$ there is $A_\eta>0$ such that, for every prime $n$ and integer $1<k\le\sqrt n$,
--   $$R(k)\le\max_{1\le i<k^2}\tau(i)\le A_\eta k^\eta,$$
--   where $\tau(i)$ is the number of positive divisors of $i$. This is the maximum divisor count, rather than an averaged divisor estimate. It is supporting development with the source's section and display citation, not an invented numbered milestone.
--
--   Differences from the source:
--   - reading: maximal divisor bound k^{o(1)} → ∀η>0, ∃Aη>0 uniform over every prime n and every allowed k; reason: the source subpolynomial bound, absorbing the finite initial k into Aη
-- source:
--   Yang S. Hu, William Kuszmaul, Jingxun Liang, Stefan Walzer, Huacheng Yu, Renfei Zhou, STOC 2027 submission #717 (October 2026), Section 6.1, unnumbered displayed R(k)≤max τ(i)=k^{o(1)}, p. 12 (PDF p. 12)

import Definitions.Def_QuadraticProbe717_Insertion_arithmetic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuadraticProbe717.Insertion

theorem small_prefix_multiplicity :
    ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 < A ∧
      ∀ (n : ℕ) [NeZero n], n.Prime → ∀ k : ℕ, 1 < k → (k : ℝ) ≤ Real.sqrt n →
        multiplicity n k ≤ maxDivisors k ∧
        (maxDivisors k : ℝ) ≤ A * (k : ℝ)^η := by sorry

end QuadraticProbe717.Insertion
