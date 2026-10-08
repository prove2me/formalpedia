-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_lower_conj
-- name    : WeightedRootIntegralIdentity.weighted_root_upper_lower_conj
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T20:21:35.38192+00:00
-- url     : https://prove2.me/theorems/3746680f-3477-4fd1-8285-776e4c917539
-- title:
--   Conjugate symmetry of the upper and lower weighted-root integrands
-- statement:
--   For real $x$, positive $\varepsilon$, real branch points $a_i$, and real weights $w_i$, define
--   $$f(z)=\frac{\prod_{i=0}^{n-1}(z-a_i)^{w_i}}{z}$$
--   using principal complex powers. Then
--   $$f(x-i\varepsilon)=\overline{f(x+i\varepsilon)}.$$
--
--   Thus the two finite-height boundary integrands are complex conjugates. This reduces their difference to an imaginary-part calculation before taking the limit $\varepsilon\to0^+$.
-- source:
--   Principal-branch conjugation symmetry used in the keyhole contour argument of K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Mathlib
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_upper_lower_conj
    (n : ℕ) (a w : ℕ → ℝ) (x ε : ℝ) (hε : 0 < ε) :
    (∏ i ∈ Finset.range n,
        (((x : ℂ) - ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) - ε * Complex.I) =
      starRingEnd ℂ
        ((∏ i ∈ Finset.range n,
            (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I)) := by sorry

end WeightedRootIntegralIdentity
