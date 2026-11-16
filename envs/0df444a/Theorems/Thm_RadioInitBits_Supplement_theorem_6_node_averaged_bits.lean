-- Prove2me | Theorems.Thm_RadioInitBits_Supplement_theorem_6_node_averaged_bits
-- name    : RadioInitBits.Supplement.theorem_6_node_averaged_bits
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:06:22.902009+00:00
-- url     : https://prove2.me/theorems/176234ae-c55e-42e7-a2c3-23e4071733d6
-- title:
--   Theorem 6 — single-bit no-CD initialization with $O(\log\log n)$ worst-case and $O(1)$ node-averaged bits, w.p. $\ge 1-1/n^2$, in $O(n)$ rounds
-- statement:
--   In the **no-CD model with single-bit messages**, initialization can be solved with $O(\log\log n)$ bits per node in the worst case and $O(1)$ bits per node on average.
--
--   Precisely, there are a family of anonymous randomized protocols $P_n$ (run on $n$ nodes that all know $n$) and an absolute constant $C$ such that for every $n\ge 3$:
--
--   1. $P_n$ runs for at most $Cn$ rounds;
--   2. in every execution, every node transmits or listens (communicates one bit) in at most $C\log\log n$ rounds;
--   3. over the nodes' independent private seeds,
--   $$\Pr\Big[\text{the outputs are not distinct IDs in }\{1,\dots,n\}\ \text{ or }\ \sum_{i=1}^{n}\mathrm{bits}_i>Cn\Big]\ \le\ \frac1{n^2},$$
--   where $\mathrm{bits}_i$ is the number of bits node $i$ communicates.
--
--   This strengthens Theorem 5 (the goal of the mission) by the node-averaged clause: the total communication of all nodes is linear in $n$ with high probability.
--
--   **Formalization Note** Stated in the published single-bit model `RadioInitBits.Protocol` (its `bits` and `Initialized`) with the published seed law. The statement is existential and does not refer to the protocol of Theorem 5.
--
--   Differences from the source:
--   - encoding: O(n) rounds, O(log log n) worst-case bits, O(1) node-averaged bits → one absolute constant C chosen before n, for all n ≥ 3; reason: the pinning of the published Theorem 5; finitely many small n are absorbed into C; natural log
--   - reading: solves 1-initialization and has round complexity O(n), worst-case bit complexity O(log log n), and node-averaged bit complexity O(1) with probability at least 1 − 1/n² → rounds and per-node bits bounded in every execution; one failure event {not initialized or total bits > C n} of probability ≤ 1/n²; reason: the paper's proof gives the round and worst-case bit bounds deterministically (as in Theorem 5) and the node-averaged bound with high probability; one joint event is the stronger reading
--   - encoding: node-averaged bit complexity (total bits over all nodes divided by n) is O(1) → ∑ᵢ bits ω i ≤ C · n; reason: multiplying by n > 0; same instances
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), short version Theorem 6, p.4 (PDF p.6); full version Theorem 6, p.4 (PDF p.25) and p.31 (PDF p.52, with proof); bit complexity definitions, p.5 (PDF p.26)

import Mathlib
import Definitions.Def_RadioInitBits_Protocol

set_option autoImplicit false

namespace RadioInitBits

namespace Supplement

open MeasureTheory

/-- **Theorem 6** (constant node-averaged bit complexity). In the no-CD model with single-bit
messages there is an anonymous randomized protocol with round complexity `O(n)` and worst-case bit
complexity `O(log log n)` that, with probability at least `1 − 1/n²`, solves initialization and has
node-averaged bit complexity `O(1)`: there are a protocol family `P` (`P n` is run on `n` nodes,
all knowing `n`) and one absolute constant `C` such that for every `n ≥ 3`

1. `P n` runs for at most `C · n` rounds;
2. in **every** execution, every node transmits or listens in at most `C · log log n` rounds;
3. the probability over the nodes' independent private seeds that the outputs are not distinct
   IDs in `{1, …, n}`, **or** that the total number of bits communicated by all `n` nodes exceeds
   `C · n`, is at most `1 / n²`.

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), short version Theorem 6, p.4 (PDF p.6): "In the no-CD
Model with single-bit messages, there exists an algorithm that solves 1-initialization and has
round complexity O(n), worst-case bit complexity O(log log n), and node-averaged bit complexity
O(1) with probability at least 1 − 1/n²"; same text in the full version, p.4 (PDF p.25) and p.31
(PDF p.52).

**Formalization Note** Stated in the published single-bit model (`RadioInitBits.Protocol`, its
`bits` and `Initialized`). `O(·)` is one constant `C` chosen before `n`, for all `n ≥ 3`; `log` is
natural. Node-averaged bit complexity `O(1)` is `(∑ᵢ bits ω i) / n ≤ C`, written as
`∑ᵢ bits ω i ≤ C · n`. "With probability at least `1 − 1/n²`" covers initialization and the
node-averaged bound jointly (one failure event); the round count and the worst-case bit bound hold
in every execution, as in Theorem 5. -/
theorem theorem_6_node_averaged_bits :
    ∃ P : ℕ → Protocol, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      ((P n).rounds : ℝ) ≤ C * n ∧
      (∀ (ω : Fin n → Seed) (i : Fin n), ((P n).bits ω i : ℝ) ≤ C * Real.log (Real.log n)) ∧
      jointSeedLaw n {ω | ¬ (P n).Initialized ω ∨ C * n < ∑ i, ((P n).bits ω i : ℝ)} ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by sorry

end Supplement

end RadioInitBits
