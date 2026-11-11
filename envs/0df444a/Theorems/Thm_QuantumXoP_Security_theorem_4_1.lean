-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_4_1
-- name    : QuantumXoP.Security.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:46.841353+00:00
-- url     : https://prove2.me/theorems/cf9cc7bb-b8ad-4b9f-a2ac-0b3f5422ce08
-- title:
--   Theorem 4.1 — quantum security of XoP[r]: $\mathrm{Adv}_q=O(\min\{q^3/N^r,q^{3/2}/N^{r-1/2},1/N^{r-3/2}\})$
-- statement:
--   Let $n,r,q$ be integers with $n\ge5$, $2\le r\le2^n/16$ and $0\le q\le2^n/57774$, and let $N=2^n$. Let $D_{XoP[r]}$ be the law of $P_1+\dots+P_r$ for independent uniformly random permutations $P_1,\dots,P_r$ of $\{0,1\}^n$, and $D_F$ the uniform distribution on all functions $\{0,1\}^n\to\{0,1\}^n$. Then every quantum algorithm making at most $q$ queries to the XOR oracle satisfies
--   $$\mathrm{Adv}^{\mathrm{dist}}_q(D_{XoP[r]},D_F)=O\Big(\min\Big\{\frac{q^3}{N^r},\ \frac{q^{3/2}}{N^{r-1/2}},\ \frac1{N^{r-3/2}}\Big\}\Big),$$
--   where the hidden constant depends only on $r$.
--
--   The theorem shows that the sum of $r$ independent random permutations is indistinguishable from a random function against quantum adversaries, with a bound that improves with $r$ and holds up to $q=\Theta(N)$ queries.
--
--   **Formalization Note** The adversary is an algorithm with any finite workspace, any number $q'\le q$ of queries, and any output map; the $P_i$ are hidden. The half-integer exponents are real powers; at $q=0$ the bound is $0$.
--
--   Differences from the source:
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 14 (PDF p. 16), Theorem 4.1

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 4.1 (p. 14, quantum security of XoP): let `n, r, q` be integers with `n ≥ 5`,
`2 ≤ r ≤ 2^n/16` and `0 ≤ q ≤ 2^n/57774`, and `N = 2^n`. Then
`Adv_q^dist(D_{XoP[r]}, D_F) = O(min{q³/N^r, q^{3/2}/N^{r−1/2}, 1/N^{r−3/2}})`,
where the hidden constant depends only on `r`. -/
theorem theorem_4_1 (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 5 ≤ n → 16 * r ≤ 2 ^ n → ∀ q : ℕ, 57774 * q ≤ 2 ^ n →
      AdvAtMost (Qubits n) (Qubits n) q (xopLaw n r) (uniformF n)
        (C * min ((q : ℝ) ^ 3 / bigN n ^ r)
          (min ((q : ℝ) ^ ((3 : ℝ) / 2) / bigN n ^ ((r : ℝ) - 1 / 2))
            (1 / bigN n ^ ((r : ℝ) - 3 / 2)))) := by sorry

end QuantumXoP.Security
