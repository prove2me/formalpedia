-- Prove2me | Theorems.Thm_QFairEx_theorem_4_8
-- name    : QFairEx.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:36.139216+00:00
-- url     : https://prove2.me/theorems/899b84af-b79c-42a0-851f-e2ae2a461515
-- title:
--   Theorem 4.8 — no perfectly secure fair exchange with a classical trusted party when $\dim S_0,\dim S_1\ge2$
-- statement:
--   Let $\mathrm{Ver}_0,\mathrm{Ver}_1$ be projective verification procedures on finite registers $\iota_0,\iota_1$ whose accepting subspaces $S_0\le\mathbb C^{\iota_0}$, $S_1\le\mathbb C^{\iota_1}$ both have dimension at least two. Then no protocol in the alternating-round communication model of Definition 4.1 — two exchange parties doing arbitrary quantum computation, a trusted party with only classical state and classical messages, any round bound $T\ge1$ — is perfectly secure against pre-determined fail-stop adversaries for $(\mathrm{Ver}_0,\mathrm{Ver}_1)$:
--   $$\dim S_0\ge2,\ \dim S_1\ge2\ \Longrightarrow\ \neg\,\mathrm{PerfectlySecure}(\Pi,S_0,S_1)\quad\text{for every valid protocol }\Pi .$$
--
--   With a trusted party that may hold quantum states, fair exchange is possible; the classical restriction is what this impossibility rests on, through the copyability of the trusted party's state.
--
--   Differences from the source:
--   - generalization: a protocol in the communication model of Definition 4.1 (exchange parties doing quantum computation, a classical trusted party) → every valid Protocol: arbitrary completely positive instruments on finite registers, classical memories and messages over arbitrary types (including a classical part of the message between the exchange parties), an auxiliary initial cq-state that may correlate all three processes; reason: the class only grows, and every protocol of the paper is one of these
--   - encoding: register and message types may change from round to round → one register type and one alphabet per process and slot for all rounds; reason: round-dependent finite registers embed isometrically into one of maximal dimension and round-dependent alphabets into their sum type, so every such protocol is simulated with identical output law
--   - encoding: after its cut the fail-stop party keeps receiving and processing but sends nothing → the stopped party's registers are traced out and its memory summed at the cut; abort is supplied in its scheduled slots and messages addressed to it are discarded; reason: its later processing acts only on its own registers and cannot change the joint state of the honest party and the trusted party (the paper's argument in the proofs of Lemmas 4.10 and 4.12)
--   - encoding: the decision and output are produced by the honest party's processing in round T → a separate decision instrument (branches acc, rej) applied after round T; reason: composing it into the round-T processing gives the same outputs
--   - reading: the honest party accepts and outputs a state supported on S_{1−b}, or rejects and outputs a state supported on S_b → the acc branch outputs on Ver_{1−b}'s register ι_{1−b}, the rej branch on Ver_b's register ι_b; reason: Definition 4.3 compares the accepted output with S_{1−b} and the rejected one with S_b
--   - generalization: Definition 4.2: the cut may be fixed or randomly sampled → PerfectlySecure quantifies over fixed cuts t ∈ {0, …, T} only; reason: a random cut is a mixture of fixed cuts, so this is a weaker hypothesis and the impossibility is stronger
--   - generalization: uniformly over a family of public verifier pairs, error bounds εcmp, εval negligible in κ taken to be zero → one fixed pair (S0, S1), no security parameter, zero error; reason: the singleton family is the weakest hypothesis; perfect security has zero error, so κ plays no role
--   - encoding: completeness and valid-state preservation also require that the exchange parties (the honest party, against a fail-stop adversary) terminate by round T → no termination clause in PerfectlySecure; reason: every execution of the model ends after round T by construction (honestState and Stop(p, t) run exactly the rounds 1, …, T), so the clause always holds
--   - encoding: projective verification procedures Ver0, Ver1 → their accepting subspaces S_b ≤ ℂ^{ι_b} (Submodule ℂ (ι_b → ℂ)), dimension as Module.finrank; reason: Definition 4.3 and Theorem 4.8 refer to Ver_b only through S_b
--   - encoding: exact-state resilience and valid-state preservation for the output conditioned on the measurement outcomes, with probability 1 → subnormalized outputs conditioned on the decision only: σ_acc = tr(σ_acc)·|ψ_{1−b}⟩⟨ψ_{1−b}|, σ_rej = tr(σ_rej)·|ψ_b⟩⟨ψ_b|, and σ_acc, σ_rej supported on S_{1−b}, S_b; reason: for a pure target, and for support on a subspace, conditioning on finer outcomes is equivalent, since positive pieces of a rank-one or S-supported operator are again so
--   - encoding: pure states |ψ⟩ → density matrices |ψ⟩⟨ψ| (vectors ι → ℂ with the standard inner product); reason: global phase is not observable; same instances
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Theorem 4.8, p.22

import Mathlib
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_PerfectlySecure

namespace QFairEx

/-- **Theorem 4.8 (no perfectly secure fair exchange with a classical trusted party).** Chung,
Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Theorem 4.8, p.22: "Let Ver0, Ver1 be projective verification
procedures whose accepting subspaces S0, S1 both have dimension at least two. No protocol in the
communication model of Definition 4.1 is perfectly secure against fail-stop adversaries for
(Ver0, Ver1)."

For all finite input registers `ι0`, `ι1` and accepting subspaces `S0 ≤ ℂ^{ι0}`, `S1 ≤ ℂ^{ι1}`
of dimension at least two, no valid protocol of the alternating-round model with a classical
trusted party (`Protocol ι0 ι1`, any round bound `T ≥ 1`, any classical alphabets, any finite
registers) is perfectly secure for `(S0, S1)`. -/
theorem theorem_4_8 {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (S0 : Submodule ℂ (ι0 → ℂ)) (S1 : Submodule ℂ (ι1 → ℂ))
    (hS0 : 2 ≤ Module.finrank ℂ S0) (hS1 : 2 ≤ Module.finrank ℂ S1)
    (P : Protocol ι0 ι1) (hP : P.IsValid) : ¬ PerfectlySecure P S0 S1 := by sorry

end QFairEx
