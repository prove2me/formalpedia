-- Prove2me | Theorems.Thm_PDSEquiv_lemma_8_6
-- name    : PDSEquiv.lemma_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:08.848787+00:00
-- url     : https://prove2.me/theorems/80bbe674-0418-4837-b726-2ae4f754fc6c
-- title:
--   Lemma 8.6 — equivalence in the binomial-$k$ model: (W̃S), (S̃S), (W̃D), (S̃D) are equivalent to (AD)
-- statement:
--   Fix rationals $0<q<p\le1$ and an infinite set $\mathcal N\subseteq\mathbb N$. The binomial-$k$ assertions (W̃S), (S̃S), (W̃D) and (S̃D) of Theorem 8.1 are equivalent to (AD), and the reductions satisfy the same parameter, running-time and oracle-query guarantees as in Lemma 8.5.
--
--   This is the right half of the equivalence of Theorem 8.1.
--
--   Differences from the source:
--   - encoding: the claims are equivalent (for every infinite 𝒩) → List.TFAE of the assertions, each an ∃ program, rational β ∈ (0, 1/2), constant, N₀ with the guarantee for all N ∈ 𝒩 with N ≥ N₀; reason: the printed assertions
--   - reading: the closing sentence: the reductions preserve (p, q), N and 𝒩, run in polynomial time, make poly(N) oracle queries on N-vertex graphs, and do not check membership in 𝒩 → a conjunct ∀ X Y in the list, Reduces p q X Y: for every β and constant of X, one oracle program, β′, a constant of Y, an exponent c and a threshold N₀ chosen before the oracle; for every oracle of X's kind, (N+2)^c time and queries on N-vertex graphs for every N and graph, and for every N ≥ N₀ the guarantee of X at size N implies that of Y at size N; reason: the sentence sits inside the theorem environment and is a claim; pointwise-in-N with no 𝒩 in it is what preserving 𝒩 without checking membership means, and it is what each arrow of the proof gives
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: an algorithm receives the graph and reads N from it; S(G) = C; D(G) ∈ {−1, 1} → input cells enc G = N :: the edge indicators of G in lexicographic pair order; a search output counts as C exactly when it is the N-bit characteristic list of C; a distinguisher accepts (value 1) exactly when it outputs [1], every other output being the value −1; reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 8.6, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_PDSEquiv_Assertions

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 8.6, p.37 (PDF p.39).
The binomial-k assertions (W̃S), (S̃S), (W̃D), (S̃D) are equivalent to (AD), through reductions in the
sense of `Reduces`. -/
theorem lemma_8_6 (p q : ℚ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (𝒩 : Set ℕ) (h𝒩 : 𝒩.Infinite) :
    List.TFAE (binomialFive.map fun A => Holds A p q 𝒩) ∧
      ∀ X ∈ binomialFive, ∀ Y ∈ binomialFive, Reduces p q X Y := by sorry

end PDSEquiv
