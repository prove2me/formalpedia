-- Prove2me | Theorems.Thm_SubexpPrimes_proposition_6_1_prime_mass
-- name    : SubexpPrimes.proposition_6_1_prime_mass
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:53.688437+00:00
-- url     : https://prove2.me/theorems/67ea1da1-6076-4efd-9732-003cfbbad9e2
-- title:
--   Proposition 6.1 — estimating the prime mass
-- statement:
--   Let $n\ge2$, let $C$ be admissible of length $L$, and let $\rho\ge0$. A dyadic $\widetilde W_C$ with
--
--   $$
--   |\widetilde W_C-W_C|\le2^{-\rho}
--   $$
--
--   can be computed in time $\mathrm{poly}(n+\rho+L)\,2^{O((n+\rho)/\sqrt{\log(n+\rho)})}$ and polynomial space.
--
--   An estimate to within a constant decides whether some prime satisfies $C$, because $W_C$ is either $0$ or at least $\ln2$.
--
--   Differences from the source:
--   - reading: deterministically, in time and space → the published PrimitiveMachine with visitedSpace, which counts every tape including the input; reason: the paper names no machine model; this is the model of the platform's proved exact_count_and_sat, and any reasonable model states the same class of bound
--   - encoding: every O(·) and poly(·) → explicit expressions with one constant, quantified before the instance; reason: the constants may depend only on the data fixed before the instance
--   - encoding: E(c(n + ρ)) for a constant c → the constant absorbed into K in 2^{K(n+ρ)/√log₂(n+ρ)}; reason: E(cx) and E(x) are the same class for x ≥ 2
--   - encoding: the input, not printed → (1ⁿ, 1^ρ, d) as one word, the output as an integer and an exponent; reason: ρ enters the bound polynomially, so unary costs nothing
--   - encoding: C admissible: constructed, and its entries computed, in time poly(n + L) → builder and entry machine of the admissible family bounded in time and space by one polynomial; reason: in the PrimitiveMachine model the visited space is at most the input length plus the number of tapes times (time + 1), and the inputs here have length polynomial in the same quantity, so a time bound gives the space bound with a larger constant; the constant is universally quantified, so no instance is lost
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Proposition 6.1, p.27

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_Admissible
import Definitions.Def_SubexpPrimes_primeMass

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Proposition 6.1 (Prime mass)** — Gajulapalli, *Deterministic Construction of Primes in Subexponential Time*
(manuscript, sha256 6ad4d3de…), p.27.

Let `n ≥ 2`, let `C` be admissible of length `L`, and let `ρ ≥ 0`. A dyadic `W̃_C` with
`|W̃_C - W_C| ≤ 2^{-ρ}` can be computed in time `poly(n + ρ + L) E(c(n + ρ))` and polynomial space.

**Formalization Note.** One machine `A` and one constant `K`, depending only on the admissible family.
The paper's `c` is absorbed: `E(cx)` and `E(x)` are the same class for `x ≥ 2`. The input is
`(1ⁿ, 1^ρ, d)`, and space is polynomial in `n + ρ + L`, input included. -/
theorem proposition_6_1_prime_mass {δ : Type} (encD : δ → List Bool)
    (C : ℕ → δ → List Bool → Prop) (hC : Admissible encD C) :
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (K : ℕ),
      ∀ (n ρ : ℕ) (d : δ), 2 ≤ n →
        ∃ (k : ℤ) (j : ℕ),
          |(k : ℝ) / 2 ^ j - primeMass n (C n d)| ≤ (2 : ℝ) ^ (-(ρ : ℤ)) ∧
          RunsWithin A out
            (Encoding.encodeList id [List.replicate n true, List.replicate ρ true, encD d])
            (dyadicWord k j)
            (subexpBound K (n + ρ + (encD d).length) (n + ρ))
            (polyBound K (n + ρ + (encD d).length)) := by sorry

end SubexpPrimes
