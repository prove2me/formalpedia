-- Prove2me | Theorems.Thm_PDSEquiv_lemma_6_5
-- name    : PDSEquiv.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:08.050509+00:00
-- url     : https://prove2.me/theorems/3b9a476a-2a79-4361-9375-5340896c0189
-- title:
--   Lemma 6.5 — decision for all larger planted sets with $n+1$ queries
-- statement:
--   There is a randomized polynomial-time oracle algorithm $B$, depending only on $q$, with the following guarantee. For every randomized distinguisher $O$ on graphs on $[n]$, $B^O$ makes $n+1$ queries on $n$-vertex graphs, outputs a value in $\{-1,1\}$, and satisfies
--
--   1. $\Pr_{B,O,\,G\sim\mathrm{ER}(n,q)}[B^O(G)=1]\le(n+1)\Pr_{O,\,G\sim\mathrm{ER}(n,q)}[O(G)=1]$;
--   2. $\Pr_{B,O,\,G\sim\mathrm{PDS}(n,j,p,q)}[B^O(G)=1]\ge\Pr_{O,\,G\sim\mathrm{PDS}(n,\kappa,p,q)}[O(G)=1]$ for all integers $0\le\kappa\le j\le n$ and every $q<p\le1$.
--
--   A guarantee at one planted size $\kappa$ thus extends to every larger planted size, at the cost of a factor $n+1$ in the null acceptance.
--
--   Differences from the source:
--   - reading: densities 0 < q < p ≤ 1 (q not said to be rational) → q rational, 0 < q < 1; p real with q < p ≤ 1 in (ii); reason: the algorithm draws exact Ber(q) bits and (i), (ii) are exact; §4.1 draws exactly only at rational probabilities and rounds irrational ones, so the exact inequalities are the paper's for rational q; every use of the lemma has q rational
--   - encoding: makes n + 1 queries → on every halted branch the number of queries is exactly n + 1; reason: the page's count, for every oracle
--   - encoding: randomized polynomial-time → ∃ e chosen before n and the oracle, log-cost and queries ≤ (n+2)^e on every branch for every oracle; reason: polynomial in the input size, uniform in the oracle
--   - encoding: a randomized oracle (distinguisher or search algorithm) on graphs → a family of laws over graphs of every size (DistFamily/SearchFamily), answering a query enc G with [1]/[0] or with the characteristic list of a set, and [] on malformed queries; the hypotheses read it at the stated size only; reason: the black-box oracle of §4.1 with fresh randomness per call; non-uniform oracles are allowed as on the page
--   - reading: randomized polynomial-time algorithm (no machine model named; unit cost for Ber(θ) with O(log N)-bit rational θ, §4.1) → a program of the log-cost RAM PDSEquiv.Machine with exact Ber(a/b) draws for any naturals a ≤ b, charged by bit lengths, halting within (N+2)^c log-cost on every random branch, for every N and every graph; reason: the paper fixes no machine; log-cost RAM time is polynomial Turing-machine time, and allowing every rational θ enlarges both sides of each claim alike while every algorithm of the paper still applies
--   - encoding: input a graph G on [n]; output a value in {−1, 1} → input cells enc G = N :: the edge indicators of G in lexicographic pair order; output [1] (value 1) or [0] (value −1); reason: the machine's input and output are lists of naturals; same instances
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 6.5, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 6.5, p.22 (PDF p.24).
A polynomial-time oracle algorithm depending only on `q`, making exactly `n + 1` queries on `n`-vertex
graphs on every branch, with the exact inequalities (i), (ii).

**Formalization Note.** `q` is rational: (i) is exact, and §4.1 draws exactly only at rational
probabilities. `P` comes before `p`, `n` and the oracle. The exponent `e` is uniform in the oracle. -/
theorem lemma_6_5 (q : ℚ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ (P : Program) (e : ℕ), ∀ (n : ℕ) (d : DistFamily),
      (∀ G : Graph n,
        HaltsWithin P (distOracle d) (enc G) ((n + 2) ^ e) ((n + 2) ^ e) ∧
          QueryCountEq P (distOracle d) (enc G) (n + 1) ∧
          QueriesSatisfy P (distOracle d) (enc G) (IsGraphQuery n) ∧
          OutputsSatisfy P (distOracle d) (enc G) IsValueOut) ∧
      expect (erMass n q) (fun G => outMass P (distOracle d) (enc G) acceptOut)
          ≤ ((n : ℝ) + 1) * expect (erMass n q) (fun G => distAcc d G) ∧
      ∀ p : ℝ, (q : ℝ) < p → p ≤ 1 → ∀ κ j : ℕ, κ ≤ j → j ≤ n →
        expect (pdsMass n j p q) (fun G => outMass P (distOracle d) (enc G) acceptOut)
          ≥ expect (pdsMass n κ p q) (fun G => distAcc d G) := by sorry

end PDSEquiv
