-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_theorem_2_1
-- name    : RSListDecodingCapacity.AllRates.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:47.964906+00:00
-- url     : https://prove2.me/theorems/acc850ae-c45b-46fb-9882-aa09e9bcee7f
-- title:
--   Theorem 2.1 (Kopparty) — finding all solutions of a polynomial differential equation
-- statement:
--   There are an absolute constant $c>0$ and one deterministic algorithm with the following property. Let $q$ be prime and $q\ge k>d$. Let $Q\in\mathbb F_q[X,Y_0,\dots,Y_d]$ be nonzero with $\deg_{Y_i}Q<q$ for all $i\in\{0,1,\dots,d\}$ and
--   $$\deg_{1,k-1,k-2,\dots,k-d-1}Q<q^2 .$$
--   Given $q,k,d$ and the terms of $Q$, the algorithm outputs, in at most $q^{c(d+1)}$ steps, the list of all $P\in\mathbb F_q[X]$ of degree at most $k-1$ satisfying
--   $$Q\big(X,P(X),P^{[1]}(X),\dots,P^{[d]}(X)\big)\equiv0, \tag{10}$$
--   each exactly once. Furthermore, the number of such $P$ is at most $q^{4d+6}$.
--
--   This is the root-finding step (step 4) of Algorithm 1. The paper cites it from Kopparty (Theorem 4.3 of [Kop15]) and gives no proof.
--
--   **Formalization Note** The algorithm is a multi-stack Turing machine over the Boolean alphabet (Mathlib's `Turing.TM2ComputableAux Bool Bool`), the time is its number of steps (`HMBinPacking.OutputsWithin`), and inputs and outputs use the binary encodings of `RSListDecodingCapacity.AllRates.Encoding`. A Turing machine simulates a bit-operation algorithm with polynomial overhead, which the constant $c$ absorbs.
--
--   Differences from the source:
--   - reading: one can find, in q^O(d+1) time, all P … → ∃ c > 0 absolute and one Turing machine M, uniform in q, k, d, Q, outputting the exact list within ⌊q^(c(d+1))⌋ steps; reason: the claim is an algorithm whose running time is q^O(d+1) with an absolute constant; d is part of the input Q ∈ 𝔽_q[X, Y_0, …, Y_d], so the algorithm is uniform in d (the stronger reading)
--   - encoding: unspecified machine model, input and output format → Turing.TM2ComputableAux Bool Bool, step count, binary input q, k, d and any term listing of Q, output the coefficient vectors of length k; reason: time bounds of the form q^O(d+1) are invariant under the polynomial simulations between machine models; the encodings are injective and polynomial-length
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.13, Theorem 2.1 (restating [Kop15, Theorem 4.3])

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Theorem 2.1** (Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, p.13;
Kopparty, Theorem 4.3, restated). There is one deterministic algorithm (a multi-stack Turing machine
`M`) and an absolute constant `c` such that: for every prime `q` and `q ≥ k > d`, and every nonzero
`Q ∈ 𝔽_q[X, Y₀, …, Y_d]` with `deg_{Y_i} Q < q` for all `i` and `deg_{1,k−1,k−2,…,k−d−1} Q < q²`,
started on `q, k, d` and any listing of the terms of `Q`, `M` outputs, within `q^{c(d+1)}` steps,
a list of all `P ∈ 𝔽_q[X]` of degree at most `k − 1` with `Q(X, P, P^{[1]}, …, P^{[d]}) ≡ 0` ((10)),
each exactly once; and that list has at most `q^{4d+6}` entries. -/
theorem theorem_2_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (q k d : ℕ), q.Prime → k ≤ q → d < k →
      ∀ Q : MvPolynomial (Option (Fin (d + 1))) (ZMod q), Q ≠ 0 →
        (∀ j : Fin (d + 1), Q.degreeOf (some j) < q) →
        Q.weightedTotalDegree (kopWeight d k) < q ^ 2 →
        ∀ l : List ((Option (Fin (d + 1)) →₀ ℕ) × ZMod q), IsTermListing Q l →
        ∃ L : List (ZMod q)[X], L.Nodup ∧
          (∀ P : (ZMod q)[X], P ∈ L ↔
            P.degree ≤ ((k - 1 : ℕ) : WithBot ℕ) ∧ hasseJetEval d Q P = 0) ∧
          HMBinPacking.OutputsWithin M (encRootFindingInput k l) (encPolyList k L)
            ⌊(q : ℝ) ^ (c * ((d : ℝ) + 1))⌋₊ ∧
          L.length ≤ q ^ (4 * d + 6) := by sorry

end RSListDecodingCapacity.AllRates
