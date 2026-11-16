-- Prove2me | Theorems.Thm_QuantumBA_PackedShares_Supplement_theorem_2
-- name    : QuantumBA.PackedShares.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:58.181583+00:00
-- url     : https://prove2.me/theorems/b48eb028-d0ed-41d1-989d-337bd5e81660
-- title:
--   Theorem 2 (companion theorem; not used in the proof of the goal) — exact communication lower bound
-- statement:
--   Let $n$ and $t$ be natural numbers with $1\le t\le n-2$. Let $P$ be any physical binary Byzantine-agreement algorithm in the synchronous full-information quantum network of §1.1. Assume that for every binary input vector and every adaptive adversary corrupting at most $t$ processes, agreement and validity hold on every execution and every correct process decides and halts with probability one. A correct process is one that is never corrupted. There is no resilience slack parameter, computation bound, fixed memory bound, or finite expected communication assumption.
--
--   Write $C_T$ and $Q_T$ for the classical bits and qubits sent while honest through the last correct halt, with each sending event placed at a boundary $T$ between staging and delivery. Classical codecs have their actual bit lengths, quantum registers are qubits, headers count as classical bits, every recipient is charged separately, and even an empty channel use costs at least one unit. For every such placement, put
--   $$
--    K_T=\sup_{x,A}\mathbb E_{x,A}[C_T+Q_T].
--   $$
--   Then
--   $$
--    K_T\ge \frac14\left\lfloor\frac{(t+1)^2}{4}\right\rfloor.
--   $$
--   The input vector $x$ and budget-limited adversary $A$ range over the entire published network model. The supremum may be infinite. This companion theorem establishes the paper's exact finite-population communication obstruction independently of the algorithm in Theorem 1; it is not used in the proof of that goal.
--
--   **Formalization Note** The sending-boundary family also includes the conservative convention that charges only messages whose senders remain honest through delivery. No correctness, no-signalling, coupling, or communication bound is built into the physical interface.
--
--   Differences from the source:
--   - encoding: n processes with binary inputs and arbitrary quantum messages → processes Fin n, inputs Bool, and registers ZMod 2 with one qubit per register; reason: each physical message is a finite list of qubits; no field-alphabet overhead or QBA parameter is imposed
--   - encoding: physical local quantum computation and classical communication in Section 1.1 → Physical P: unitary local gates with fresh zero ancillas and computational-basis measurements, injective bit-string codecs of actual length, distinct outgoing wires, and equivariance under injective register renaming; reason: finite quantum instruments can be implemented by unitary dilation and measurement; register names are opaque implementation handles rather than an additional uncharged communication channel; invalid local encodings may be sanitized on unreachable states; fresh handles may be recorded in local preparation steps before use, with no additional communication, and Theorem 2 has no round bound
--   - encoding: every input and adversary corrupting at most t processes → SolvesBinaryBA P t universally quantifies input vectors and the published Adversary, whose corruption requests are capped at t by the published execution semantics; reason: all strategies within the corruption budget are retained, including rushing, suppression and growing memory; no upper-bound resilience constraint is used
--   - encoding: agreement and validity on every execution and termination with probability 1 → the published Agreement, Validity and Termination predicates, with correct meaning never corrupted; reason: these are the published semantics of the source correctness premise; termination includes decision and halt and has no finite-expectation requirement
--   - generalization: C and Q count bits and qubits sent while honest → the bound holds for every placement T of each staged transmission's sending event at a boundary between staging and delivery, charging it only if its sender is honest there, including the smallest honest-through-delivery counter; reason: any source sending boundary specializes this accounting; permanent corruption makes the delivery counter no larger than the source count, and all U senders in the Section 7 reference executions stay correct, so the proof retains every transmission it needs
--   - encoding: K = sup over x,A of E[C+Q], allowing infinity, with costs through the last correct halt → worstCommunication is an ENNReal iterated supremum outside the lower Lebesgue integral of sourceC + sourceQ, with nonnegative series through the imported roundsR cutoff; reason: ENNReal retains unbounded costs as infinity, never default zero; the two costs are combined before expectation and supremum; rounds use the published completed-round halt convention
--   - encoding: one quarter times floor of (t+1) squared divided by four → (((t+1)^2 / 4 : Nat) : ENNReal) / 4; reason: natural division implements exactly the inner floor, and the outer division is in ENNReal; t=1 gives 1/4, t=2 gives 1/2, and t=3 gives 1
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), p. 2, Theorem 2 (PDF 3); proof pp. 34–35, Section 7 (PDF 35–36)

import Definitions.Def_QuantumBA_PackedShares_Supplement_Communication

set_option autoImplicit false

open scoped ENNReal

namespace QuantumBA.PackedShares.Supplement

/-- Theorem 2 (§1.2, proof §7): exact finite-n lower bound for arbitrary physical binary BA
algorithms, including infinite worst-case expectation. The assertion is uniform over sending
boundaries between staging and delivery; in particular it includes the conservative
honest-through-delivery counter, which is no larger than any source honest-sent counter. -/
theorem theorem_2 (n t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n - 2)
    (P : Protocol n Qubit) (hphysical : Physical P) (hBA : SolvesBinaryBA P t)
    (T : SendTiming P) :
    (((t + 1) ^ 2 / 4 : ℕ) : ℝ≥0∞) / 4 ≤ worstCommunication P t T := by sorry

end QuantumBA.PackedShares.Supplement
