-- Prove2me | Theorems.Thm_RadioInitBits_theorem_5_reduced_bit_initialization
-- name    : RadioInitBits.theorem_5_reduced_bit_initialization
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:50.452212+00:00
-- url     : https://prove2.me/theorems/cf5ab66a-cf02-4edc-bff9-29790003bf72
-- title:
--   Theorem 5 — without collision detection and with single-bit messages, $n$ anonymous nodes get IDs $1,\dots,n$ w.p. $\ge 1-1/n^2$ in $O(n)$ rounds with $O(\log\log n)$ bits per node
-- statement:
--   Consider a single-hop radio network of $n$ identical nodes that all know $n$. The nodes have independent private randomness and no identifiers. The channel has no collision detection: a listener hears a message only when exactly one node transmits, and otherwise hears silence. Messages are single bits.
--
--   There exist a protocol family $(P_n)_{n\ge1}$ and an absolute constant $C$ such that for every $n\ge3$:
--
--   1. $P_n$ runs for at most $Cn$ rounds;
--   2. in every execution, every node transmits or listens in at most $C\log\log n$ rounds, so it communicates at most $C\log\log n$ bits (a listen that hears silence counts as one bit);
--   3. with probability at least $1-1/n^2$ over the nodes' seeds, the nodes output pairwise distinct IDs in $\{1,\dots,n\}$:
--   $$\Pr\big[\text{the outputs are not a bijection onto }\{1,\dots,n\}\big]\ \le\ \frac{1}{n^2}.$$
--
--   Earlier initialization protocols transmit $\Theta(\log n)$-bit IDs, so each node communicates $\Omega(\log n)$ bits. This theorem needs exponentially fewer bits per node, $O(\log\log n)$. The paper's lower bound (Theorem 1) shows this cannot be improved asymptotically, even with collision detection.
--
--   **Formalization Note** The protocol model, the bit count and the success event are those of the definition `RadioInitBits.Protocol`. The logarithm is natural; the base changes only $C$.
--
--   Differences from the source:
--   - encoding: round complexity O(n) and bit complexity O(log log n) → one constant C, chosen before n, with rounds ≤ C·n and bits ≤ C·ln ln n for every n ≥ 3; reason: the two forms are equivalent, since the finitely many n below any threshold are absorbed into C, and the base of the logarithm changes only C; n ≥ 3 makes ln ln n > 0
--   - reading: "has round complexity O(n) and bit complexity O(log log n)" next to "with probability at least 1 − 1/n²" → the round and bit bounds hold in every execution, for every node; reason: the paper defines bit complexity as a maximum over nodes (p.5), and the bounds sit outside "with probability" in the sentence; the stronger reading
--   - reading: "Algorithm 8 solves 1-initialization" (full version) → "there exists an algorithm" (short version, Theorem 5, p.4); reason: the two versions of the same theorem differ; Algorithm 8 as printed is not a complete, consistent protocol (see the mission's notes on Lemmas 30 and 34), and the short version states the theorem existentially
--   - encoding: randomized identical nodes → every node runs the same code, with no identifier, on a private seed of independent uniform numbers in [0,1], seeds independent across nodes; reason: a stream of independent uniforms is a universal source of private randomness; the protocol cannot choose its own
--   - encoding: "with probability at least 1 − 1/n²" → the probability of the failure set is at most 1/n²; reason: complement form; it needs no measurability side condition
--   - encoding: an algorithm run by every node → a protocol whose local rules (init, act, update, output) are arbitrary functions, not required to be computable or measurable; reason: the paper places no condition on a node's local computation, its claims are about what the channel lets anonymous nodes achieve, and the success clause bounds the outer measure of the failure set, so it still demands a measurable event of probability at least 1 − 1/n² on which every node succeeds
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), short version Theorem 5, p.4 (PDF p.6) and §5.2, p.14 (PDF p.16); full version Theorem 5, p.4 (PDF p.25) and p.30 (PDF p.51)

import Mathlib
import Definitions.Def_RadioInitBits_Protocol

set_option autoImplicit false

namespace RadioInitBits

open MeasureTheory

/-- **Theorem 5** (reduced-bit initialization). In the no-CD model with single-bit messages there
is an anonymous randomized protocol that solves initialization with probability at least
`1 − 1/n²`, has round complexity `O(n)`, and has bit complexity `O(log log n)`: there are a
protocol family `P` (`P n` is run on `n` nodes, all knowing `n`) and one absolute constant `C`
such that for every `n ≥ 3`

1. `P n` runs for at most `C · n` rounds;
2. in **every** execution, every node transmits or listens in at most `C · log log n` rounds
   (each such round is one bit communicated);
3. the probability over the nodes' independent private seeds that the outputs are not distinct
   IDs in `{1, …, n}` is at most `1 / n²`.

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), short version Theorem 5, p.4 (PDF p.6): "In the no-CD
Model with single-bit messages, there exists an algorithm that solves 1-initialization with
probability at least 1 − 1/n² and has round complexity O(n) and bit complexity O(log log n)";
full version Theorem 5, p.4 (PDF p.25) and p.30 (PDF p.51), with "Algorithm 8" in place of
"there exists an algorithm".

**Formalization Note** `O(·)` is one constant `C` chosen before `n`, for all `n ≥ 3` (so that
`log log n > 0`; finitely many small `n` can be absorbed into `C`). `log` is the natural
logarithm (the base changes only `C`). The round and bit bounds hold in every execution
(worst case), and the bit bound is a maximum over nodes, as in the paper's definition of bit
complexity (p.5). The success clause bounds the (outer) measure of the failure set. The protocol
is existential, as in the short version; the full version's Algorithm 8 is one witness. -/
theorem theorem_5_reduced_bit_initialization :
    ∃ P : ℕ → Protocol, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      ((P n).rounds : ℝ) ≤ C * n ∧
      (∀ (ω : Fin n → Seed) (i : Fin n), ((P n).bits ω i : ℝ) ≤ C * Real.log (Real.log n)) ∧
      jointSeedLaw n {ω | ¬ (P n).Initialized ω} ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by sorry

end RadioInitBits
