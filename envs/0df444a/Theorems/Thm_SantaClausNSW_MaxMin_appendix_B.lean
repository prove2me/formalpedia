-- Prove2me | Theorems.Thm_SantaClausNSW_MaxMin_appendix_B
-- name    : SantaClausNSW.MaxMin.appendix_B
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:36:02.175601+00:00
-- url     : https://prove2.me/theorems/594717ee-9b83-45fb-b134-138bb349e56d
-- title:
--   Appendix B — under the bit bound, ordinary demand queries implement restricted demand queries and exact value evaluation
-- statement:
--   Assume every value $v_i(S)$ is $a/b$ with $a,b\le2^\sigma$.
--
--   *Restricted demand.* To restrict a demand query to $R$, keep the given nonnegative prices on $R$ and price every other item at $2^\sigma+1$; then every set maximizing $v_i(D)-p'(D)$ over all sets lies in $R$ and maximizes $v_i(D)-p(D)$ among the subsets of $R$.
--
--   *Exact value evaluation.* Using ordinary demand queries one recovers $v_i(S)$ exactly with $O(|S|\sigma)$ queries, by binary search on each marginal value and continued fractions, in polynomial time.
--
--   These implementations let the subadditive algorithms (Lemmas 3.4, 3.7, Theorem 3.12) use only ordinary demand queries.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithm (no machine model is named) → a program on the mission's RAM over exact rationals (fair coins, an oracle port; bit-cost work), every run halting within c·(1 + size)^d work, c and d fixed before the input; reason: the paper fixes no model; worst-case polynomial bit cost with constants chosen before the instance is the standard meaning of polynomial time
--   - encoding: agents N, items M, valuations 2^M → R≥0 → Fin n, Fin m, v : Finset (Fin m) → ℝ normalized and monotone; reason: Lean convention; nonnegativity follows from normalization and monotonicity; same instances
--   - encoding: oracle queries with ties broken arbitrarily → an oracle is any fixed answer function correct on every well-formed question, quantified universally outside the probability over the coins; reason: the standard reading of 'ties broken arbitrarily'; malformed questions are unconstrained, so the program cannot rely on them
--   - reading: O(|S|σ) ordinary demand queries → at most c·|S|·(σ + 1) demand queries, c fixed before the input; reason: σ may be 0 (values in {0, 1}), where O(|S|σ) must still allow one query per item
--   - reading: 'gives the implementation of value … queries under this convention' (§2) → the evaluation program also halts within c·(1 + n + m + σ)^d work on input n, m, σ, i, 1_S; reason: Appendix B states the continued-fraction step runs in polynomial time; the implementation is used inside polynomial-time algorithms
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 62, Appendix B

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Oracles

namespace SantaClausNSW.MaxMin

/-- **Appendix B** (p. 62). Under the bound `v_i(S) = a/b`, `a, b ≤ 2^σ`:
(restricted demand) pricing every item outside `R` at `2^σ + 1` and keeping the nonnegative
prices on `R`, every set maximizing the ordinary demand objective lies in `R` and maximizes the
objective among the subsets of `R`;
(exact value evaluation) there are a program and constants `c, d` that, with any correct
ordinary demand oracle, compute `v_i(S)` exactly within `c (1 + n + m + σ)^d` work using at most
`c · |S| · (σ + 1)` demand queries. -/
theorem appendix_B :
    (∀ (n m σ : ℕ) (v : Fin n → Finset (Fin m) → ℝ), (∀ i, IsValuation (v i)) →
      BitBounded v σ → ∀ (i : Fin n) (R : Finset (Fin m)) (p : Fin m → ℚ), (∀ j, 0 ≤ p j) →
      ∀ D : Finset (Fin m),
        IsDemandSet (v i) (fun j => if j ∈ R then p j else 2 ^ σ + 1) Finset.univ D →
        IsDemandSet (v i) p R D) ∧
    (∃ (P : Program) (c d : ℕ), ∀ (n m σ : ℕ), 0 < n →
      ∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsValuation (v i)) → BitBounded v σ →
      ∀ O : Oracle, IsDemandOracle v O → ∀ (i : Fin n) (S : Finset (Fin m)),
        HaltsWithin P O (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: encSet S))
          (c * (1 + oracleSize n m σ) ^ d) ∧
        ∀ s ∈ (run P O (c * (1 + oracleSize n m σ) ^ d + 1)
            (initState (oracleInput n m σ ++ (((i : ℕ) : ℚ) :: encSet S)))).support,
          s.queries ≤ c * S.card * (σ + 1) ∧
          ∃ r : ℚ, (outList s.mem).head? = some r ∧ (r : ℝ) = v i S) := by sorry

end SantaClausNSW.MaxMin
