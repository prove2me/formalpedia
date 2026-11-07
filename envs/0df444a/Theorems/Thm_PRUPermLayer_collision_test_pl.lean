-- Prove2me | Theorems.Thm_PRUPermLayer_collision_test_pl
-- name    : PRUPermLayer.collision_test_pl
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:40.841831+00:00
-- url     : https://prove2.me/theorems/4ba6b28b-f3d3-4339-920b-e657448d16ef
-- title:
--   Proof of Theorem 1.1(ii), p.19 — the collision test accepts $PL$ with probability $\ge Kq - \binom K2 2^{-n}$
-- statement:
--   Let $t \ge 2$, $K = \binom t2$ and $q = (2/3)^n$. The $t$-query collision test (query $|0^n\rangle$ $t$ times, measure every output in the computational basis, accept if two outcomes are equal) accepts the oracle $PL$ with probability
--   $$
--   \Pr[\text{accept} \mid PL] \ge Kq - \binom K2 2^{-n} .
--   $$
--
--   This is the construction side of the attack that proves the lower half of Theorem 1.1(ii).
--
--   Differences from the source:
--   - encoding: $\Pr[\text{accept}\mid PL]$ → the expectation over $U \sim PL$ of the test's acceptance probability for the fixed oracle $U$; reason: the oracle is sampled once; same number
--   - encoding: $2^{-n}$ → $(1/2)^n$; reason: same number
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_PRUPermLayer_plEnsemble
import Definitions.Def_PRUPermLayer_collisionAccept
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Collision test on `PL`** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), proof of Theorem 1.1, part (ii), lower bound, p.19 (PDF
p.21)). Let `t ≥ 2`, `K = C(t, 2)` and `q = (2/3)ⁿ`. The `t`-query collision test (query `|0ⁿ⟩`
`t` times, measure every output in the computational basis, accept if two outcomes are equal)
accepts the oracle `PL` with probability `Pr[accept | PL] ≥ Kq − C(K, 2) 2⁻ⁿ`.

**Formalization Note** `Pr[accept | PL]` is the expectation over `U ∼ PL` of `collisionAccept n t U`,
the probability that `t` independent samples of `p_x = |⟨x|U|0ⁿ⟩|²` are not pairwise different.
`2⁻ⁿ` is `(1/2)ⁿ`. -/
theorem collision_test_pl (n t : ℕ) (ht : 2 ≤ t) :
    (t.choose 2 : ℝ) * (2 / 3 : ℝ) ^ n - ((t.choose 2).choose 2 : ℝ) * (1 / 2 : ℝ) ^ n ≤
      ∫ U, collisionAccept n t (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        ∂(plEnsemble n) := by sorry

end PRUPermLayer
