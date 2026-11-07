-- Prove2me | Theorems.Thm_PRUPermLayer_collision_test_haar
-- name    : PRUPermLayer.collision_test_haar
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:31.087005+00:00
-- url     : https://prove2.me/theorems/f1306dff-5adc-40f6-9626-7b10fa9cb478
-- title:
--   Proof of Theorem 1.1(ii), p.20 — the collision test accepts Haar with probability $\le 2K/(N+1)$
-- statement:
--   Let $t \ge 2$, $K = \binom t2$ and $N = 2^n$. The $t$-query collision test accepts a Haar-random oracle with probability
--   $$
--   \Pr[\text{accept} \mid \mathrm{Haar}] \le \frac{2K}{N+1} .
--   $$
--
--   With the bound for $PL$ it shows that the collision test has advantage $(1 - o(1))\binom t2 (2/3)^n$.
--
--   Differences from the source:
--   - encoding: $\Pr[\text{accept}\mid \mathrm{Haar}]$ → the expectation over Haar-random $U$ of the test's acceptance probability for the fixed oracle $U$; reason: same number
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_PRUPermLayer_haar
import Definitions.Def_PRUPermLayer_collisionAccept
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Collision test on Haar** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.20 (PDF
p.22)). Let `t ≥ 2` and `K = C(t, 2)`. The `t`-query collision test accepts a Haar-random oracle
with probability `Pr[accept | Haar] ≤ 2K/(N + 1)`, `N = 2ⁿ`.

**Formalization Note** `Pr[accept | Haar]` is the expectation over `U ∼ Haar` of
`collisionAccept n t U`. -/
theorem collision_test_haar (n t : ℕ) (ht : 2 ≤ t) :
    ∫ U, collisionAccept n t (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ∂(haar n) ≤
      2 * (t.choose 2 : ℝ) / (2 ^ n + 1) := by sorry

end PRUPermLayer
