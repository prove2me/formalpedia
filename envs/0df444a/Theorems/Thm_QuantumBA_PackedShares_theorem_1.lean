-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_theorem_1
-- name    : QuantumBA.PackedShares.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:52.24556+00:00
-- url     : https://prove2.me/theorems/93424195-23ad-4965-8853-2a146e4088bf
-- title:
--   Theorem 1 — QBA:PackedShares: Byzantine agreement for t ≤ (1/3−ε)n with E[Q] = O_ε(n log⁸n), E[C] = O_ε(n² log⁸n), E[R] = O_ε(log⁴n)
-- statement:
--   Fix $0<\varepsilon<1/3$. There is a constant $C_\varepsilon$ such that for every $n$ and every $t\le(1/3-\varepsilon)n$, the algorithm QBA:PackedShares (with the parameters (11)), in the model of §1.1 against every adversary corrupting at most $t$ processes and for every input vector, satisfies agreement and validity on every execution and terminates with probability $1$, and its expected costs satisfy, with $\Lambda=\max\{1,\log_2n\}$,
--   $$\mathbb E[Q]\le C_\varepsilon\,n\Lambda^8,\qquad\mathbb E[C]\le C_\varepsilon\,n^2\Lambda^8,\qquad\mathbb E[R]\le C_\varepsilon\,\Lambda^4 .$$
--
--   This is the main result of the paper: Byzantine agreement against a full-information adaptive adversary that may suppress messages in transit, with nearly linear quantum communication and, by Theorem 2, near-optimal total communication.
--
--   Differences from the source:
--   - encoding: processes hold quantum registers; the adversary has an arbitrary finite-dimensional quantum memory and applies arbitrary joint quantum instruments → all registers are F-valued qudits (one field element = d qubits) named by natural numbers, unallocated registers in |0⟩; the adversary may claim any number of fresh registers in every micro-step and applies instruments with one Kraus operator per outcome; reason: any finite-dimensional memory embeds into finitely many qudits and any instrument is realized by one Kraus operator per outcome after adjoining ancillas (Stinespring), so no adversary is lost; the memory may grow without bound
--   - reading: corruptions may happen at any boundary, including inside a round; the adversary is rushing → each round consists of n+1 adversarial micro-steps (instrument, then optionally one more corruption), the honest step (operations, measurements, staging of messages), n+1 adversarial micro-steps that see the staged messages, and delivery; reason: n+1 alternations per slot allow every corruption pattern (at most n corruptions); the slot after delivery covers corruption between receiving and computing, the slot before delivery covers rushing and seizing messages in transit
--   - encoding: adversaries that corrupt at most t processes → the semantics ignores a corruption request once t processes are corrupted; reason: this maps every strategy onto one in the class and leaves strategies in the class unchanged
--   - generalization: qubits and classical bits sent while honest → every transmission staged by a process honest at the honest step is charged, even if the sender is corrupted later in the round; reason: a larger count; the paper notes its upper bounds also hold for it (§1.1, PDF 3)
--   - encoding: classical messages are bit strings; missing or malformed votes count as ⊥ → classical messages are values of the message type Msg with an explicit self-delimiting bit length; a quantum message is a list of (array, label, register) entries charged d qubits per register and its headers as classical bits; every channel use costs at least one unit; reason: a malformed string is treated exactly like a missing message, so restricting Byzantine senders to well-formed values changes no honest behaviour; the bit lengths are those of a concrete encoding
--   - encoding: agreement and validity on every execution; termination with probability 1; expectations of Q, C, R → the law of an execution is the Ionescu–Tulcea measure of the Born-rule step kernels on infinite outcome sequences; an execution is an outcome sequence all of whose finite prefixes have positive probability; expectations are lower Lebesgue integrals of ℝ≥0∞-valued costs counted through the last halt of a correct process; reason: standard encoding of the probability space of the full-information model; no integrability side condition is needed
--   - generalization: a fixed field F_q with q = 2^d, a fixed nonzero F2-linear ψ, fixed distinct nonzero evaluation points, a fixed F2-basis → the statement holds for every field F with |F| = 2^d, every additive ψ : F → ZMod 2 with ψ ≠ 0, every injective nonzero α : Fin n → F (a block with D outputs uses α_1, …, α_D) and every additive equivalence F ≃ (Fin d → ZMod 2); reason: the paper fixes arbitrary such choices; the statement for all of them specializes to any fixed one
--   - reading: all processes use the first valid assignment (forwarding graph) in a fixed public order → committeeTable / forwardingGraph take the valid indicator table with least Encodable.encode, a fixed default if none exists; graphs are taken on committee positions, one per level; reason: a concrete fixed public order; the proofs only use validity
--   - reading: round structure of an election: bin round, coin phases of four rounds, delivery; 1 + h(4bw+3) + 4(w+1) rounds per epoch → per level: bin round (holders open bin words, members request), reply round, r phases of four rounds (estimates, proposals, coin request with opening, reply and update), delivery round with list delivery and Algorithm 2; then w+1 final phases; reason: this realizes the round count of §6.4 and the opening and request rules of §3.2
--   - reading: a recipient accepts at most one register per authorized array, word and incoming edge; replies carry address–value pairs → a register for array x and word λ is accepted from sender s only if s is an in-neighbour (or the dealer of x at distribution), the first such entry from s; an address is (level of the producing block, its holder); requests and replies carry the node tag; reason: a concrete instance of the rules of §2.4 and §3.2, which leave the encoding of authorization and addresses open
--   - encoding: O_ε(n log⁸ n), O_ε(n² log⁸ n), O_ε(log⁴ n) → one constant C(ε) > 0 for every n, every t ≤ (1/3−ε)n, every input vector, adversary and public choice, with log n read as Λ = max(1, log₂ n); reason: O_ε means a constant depending only on ε; for n ≥ 2 Λ = log₂ n, and Λ = 1 makes the n = 1 case (decide at once, send nothing) non-degenerate
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, p. 2, Theorem 1 (PDF p. 3); proof §6.5, pp. 33–34 (PDF 34–35)

import Mathlib
import Definitions.Def_QuantumBA_PackedShares_Analysis

namespace QuantumBA.PackedShares

open scoped BigOperators ENNReal Matrix

/-- Theorem 1: QBA:PackedShares satisfies agreement and validity on every execution, terminates
with probability 1, and has expected costs `E[Q] = O_ε(n log⁸ n)`, `E[C] = O_ε(n² log⁸ n)`,
`E[R] = O_ε(log⁴ n)`, with one constant per `ε`, uniform over `n`, `t ≤ (1/3 - ε)n`, the inputs,
the adversary and the public choices; `log n` is read as `max(1, log₂ n)`. -/
theorem theorem_1 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n t : ℕ), (t : ℝ) ≤ (1 / 3 - ε) * n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], Fintype.card F = 2 ^ parDbits n →
      ∀ (cf : Choices n F), Function.Injective cf.α → (∀ i, cf.α i ≠ 0) → cf.ψ ≠ 0 →
      ∀ (x : Fin n → Bool) (A : Adv (ctx11 ε n t cf)),
        let P := qba (ctx11 ε n t cf)
        let Λn : ℝ := max 1 (Real.logb 2 n)
        Agreement P x A t ∧ Validity P x A t ∧ Termination P x A t ∧
        expect P x A t (costQ P x A t) ≤ ENNReal.ofReal (C * n * Λn ^ 8) ∧
        expect P x A t (costC P x A t) ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2 * Λn ^ 8) ∧
        expect P x A t (fun ω => (roundsR P x A t ω : ℝ≥0∞)) ≤ ENNReal.ofReal (C * Λn ^ 4) := by sorry

end QuantumBA.PackedShares
