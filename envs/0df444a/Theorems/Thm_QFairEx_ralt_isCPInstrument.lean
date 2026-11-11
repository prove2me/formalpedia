-- Prove2me | Theorems.Thm_QFairEx_ralt_isCPInstrument
-- name    : QFairEx.ralt_isCPInstrument
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:27:40.817094+00:00
-- url     : https://prove2.me/theorems/04fff1b1-bb39-41de-9056-df98e6ff44c3
-- title:
--   Algorithm 4.11 — $R_{\mathrm{alt}}(t)$ is an adversary of the parallel BB84 game with $n=2$
-- statement:
--   For every valid protocol, orthonormal encoding pairs $e_0,e_1$ and every cut $t\le T$, the reduction $R_{\mathrm{alt}}(t)$ of Algorithm 4.11 is a physical adversary of the parallel BB84 basis guessing game with two challenge states: each of its answer branches $(j,\theta^*)$ is completely positive in the two challenge qubits, and the answer probabilities add up to the trace of the input.
--
--   This is what makes Theorem 4.5 applicable to the reduction; it rests on the trusted party's state being classical, so that it can be copied.
--
--   Differences from the source:
--   - generalization: a protocol in the communication model of Definition 4.1 (exchange parties doing quantum computation, a classical trusted party) → every valid Protocol: arbitrary completely positive instruments on finite registers, classical memories and messages over arbitrary types (including a classical part of the message between the exchange parties), an auxiliary initial cq-state that may correlate all three processes; reason: the class only grows, and every protocol of the paper is one of these
--   - encoding: register and message types may change from round to round → one register type and one alphabet per process and slot for all rounds; reason: round-dependent finite registers embed isometrically into one of maximal dimension and round-dependent alphabets into their sum type, so every such protocol is simulated with identical output law
--   - encoding: after its cut the fail-stop party keeps receiving and processing but sends nothing → the stopped party's registers are traced out and its memory summed at the cut; abort is supplied in its scheduled slots and messages addressed to it are discarded; reason: its later processing acts only on its own registers and cannot change the joint state of the honest party and the trusted party (the paper's argument in the proofs of Lemmas 4.10 and 4.12)
--   - encoding: the decision and output are produced by the honest party's processing in round T → a separate decision instrument (branches acc, rej) applied after round T; reason: composing it into the round-T processing gives the same outputs
--   - reading: the honest party accepts and outputs a state supported on S_{1−b}, or rejects and outputs a state supported on S_b → the acc branch outputs on Ver_{1−b}'s register ι_{1−b}, the rej branch on Ver_b's register ι_b; reason: Definition 4.3 compares the accepted output with S_{1−b} and the rejected one with S_b
--   - reading: D_p applies U_p† to the register and discards the ancillary qubits, for a unitary U_p implementing E_p → D_p(σ) = E_p†σE_p + tr((I − E_pE_p†)σ)|0⟩⟨0|; reason: the paper's D_p presupposes a qubit register and depends on the choice of U_p; only its property D_p(E_pρE_p†) = ρ is used, which this CPTP map has
--   - encoding: game index j ∈ {1, 2}, challenge 1 to P0 and challenge 2 to P1 → j : Fin 2 (0-based), qubit 0 encoded by E0 for P0 and qubit 1 by E1 for P1; reason: renaming of indices
--   - encoding: pure states |ψ⟩ → density matrices |ψ⟩⟨ψ| (vectors ι → ℂ with the standard inner product); reason: global phase is not observable; same instances
--   - generalization: encodings e_{p,0}, e_{p,1} ∈ S_p → orthonormal pairs e_0, e_1 in arbitrary registers, not required to lie in accepting subspaces; reason: membership in S_p is not used; the paper's encodings are a special case
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.2.2, p.22, and Algorithm 4.11, p.24

import Mathlib
import Definitions.Def_QFairEx_IsCPInstrument
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_Protocol_ralt

namespace QFairEx

/-- **R_alt(t) is an adversary of the parallel BB84 game with `n = 2`.** Chung, Lee, Raizes,
Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256
0099b883…), §4.2.2, p.22 ("We prove the theorem by constructing an adversary for the parallel
BB84 basis guessing game with two challenge states") and Algorithm 4.11, p.24.

For every valid protocol, orthonormal encodings `e0`, `e1` and cut `t ≤ T`, the reduction
`R_alt(t)` is a completely positive instrument from the two challenge qubits to the answer
`(j, θ*) ∈ Fin 2 × Bool`: every answer branch is completely positive and the answer
probabilities sum to the input trace. -/
theorem ralt_isCPInstrument {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0]
    [DecidableEq ι1] (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (he0 : IsOrthonormalPair e0) (he1 : IsOrthonormalPair e1)
    (P : Protocol ι0 ι1) (hP : P.IsValid) (t : ℕ) (ht : t ≤ P.T) :
    IsCPInstrument (P.ralt e0 e1 t) := by sorry

end QFairEx
