-- Prove2me | Theorems.Thm_PermutationStreams_Parity_communication_lower_bound
-- name    : PermutationStreams.Parity.communication_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:15.590448+00:00
-- url     : https://prove2.me/theorems/a35bae47-73d8-42e8-98ea-2b71cde1b5c2
-- title:
--   Lemma 4.4 — randomized three-party communication lower bound for $f_m$
-- statement:
--   Consider the three-party number-in-hand problem of computing $f_m$: Alice knows $x\in[3]^m$, Bob knows $y\in[3]^m$, Charlie knows $z\in[3]^m$, and every coordinate triple $(x_i,y_i,z_i)$ is promised to be a permutation of $[3]$. The players write bits on a common blackboard, may use public randomness, and may communicate for any number of rounds.
--
--   There is a constant $\alpha>0$ for which the bound of Lemma 4.3 holds, and for **every** such $\alpha$ the following is true. Let $m\ge0$ and $\delta<1/2$. If a public-coin randomized protocol outputs $f_m(x,y,z)$ with error probability at most $\delta$ on each promised input, and writes at most $L$ bits on every promised input for every outcome of the coins, then
--
--   $$
--   L\ \ge\ \alpha m+\log_2(1-2\delta).
--   $$
--
--   In particular error at most $1/3$ requires at least $\alpha m-\log_2 3$ bits. This is the communication bound to which the streaming lower bound is reduced; since rounds are unrestricted it also covers multi-pass simulations.
--
--   **Formalization Note** Protocols are binary trees whose leaves carry the output (see the protocol definition); the cost is the number of bits written in the actual execution, bounded on promised inputs. "The constant in Lemma 4.3" is read as any constant for which the Lemma 4.3 inequality holds, together with the existence of a positive one.
--
--   Differences from the source:
--   - reading: α is the constant in Lemma 4.3 → a positive α satisfying the Lemma 4.3 bound exists, and the communication bound holds for every α satisfying it; reason: the stronger of the two readings; the proof uses only the Lemma 4.3 inequality
--   - generalization: protocols whose output bit is written on the board and counted → protocols whose output is a leaf label, cost counting written bits only; reason: a source protocol of cost L is such a tree of cost at most L, so the Lean bound applies to it
--   - encoding: communicates at least B bits in the worst case → every bound L on the cost over all coins and promised inputs satisfies L ≥ B; reason: equivalent to the maximum cost being at least B
--   - encoding: 0 ≤ δ < 1/2 → δ < 1/2; reason: an error probability is nonnegative, so negative δ admits no protocol
--   - encoding: x, y, z ∈ [3]^m, coordinates 1,…,m → Fin m → Fin 3; reason: order-preserving relabelling
--   - encoding: a protocol defined on promised inputs → a tree defined on all of [3]^m with cost and error constrained on promised inputs only; reason: behavior off the promise is unconstrained, so any source protocol extends arbitrarily
--   - encoding: public randomness → a finite probability space of coin outcomes selecting deterministic trees; reason: on finite inputs only finitely many behaviors of cost at most L exist, so any coin distribution induces such a mixture
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, p. 7, Lemma 4.4 (model described in the paragraph preceding it)

import Definitions.Def_PermutationStreams_Parity_SignProblem
import Definitions.Def_PermutationStreams_Parity_Protocols

namespace PermutationStreams.Parity

/-- Braverman–Zamir, Lemma 4.4, p.7. A constant `α > 0` as in Lemma 4.3 exists, and for every
`α` for which the Lemma 4.3 bound holds: every public-coin three-party number-in-hand protocol
computing `f_m` with error at most `δ < 1/2` on each promised input, and writing at most `L`
bits on every promised input under every coin outcome, has `L ≥ αm + log₂(1 - 2δ)`. -/
theorem communication_lower_bound :
    (∃ α : ℝ, 0 < α ∧ SignCorrelationBound α) ∧
    ∀ α : ℝ, SignCorrelationBound α →
      ∀ (m : ℕ) (δ : ℝ), δ < 1 / 2 →
      ∀ {Ω : Type} [Fintype Ω]
        (P : PublicCoinProtocol3 Ω (Fin m → Fin 3) (Fin m → Fin 3) (Fin m → Fin 3) ℤˣ)
        (L : ℕ),
        (∀ ω x y z, Promised m x y z → (P.tree ω).cost x y z ≤ L) →
        (∀ x y z, Promised m x y z → P.errorProb x y z (fm m x y z) ≤ δ) →
        α * m + Real.logb 2 (1 - 2 * δ) ≤ L := by sorry

end PermutationStreams.Parity
