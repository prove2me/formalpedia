-- Prove2me | Theorems.Thm_QFairEx_lemma_4_12
-- name    : QFairEx.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:27:56.394415+00:00
-- url     : https://prove2.me/theorems/66629350-b869-48c6-9729-141df9c2bb3a
-- title:
--   Lemma 4.12 — $\Pr[R_{\mathrm{alt}}(t)\text{ wins}]=\tfrac12+\tfrac{\delta_t}4\ge\tfrac12+\tfrac{|p_0(t)-p_1(t)|}4$
-- statement:
--   Let a valid protocol be perfectly secure against fail-stop adversaries for $S_0,S_1$, and let the encodings use orthonormal $e_{p,0},e_{p,1}\in S_p$. For every cut $t\le T$, with $\delta_t=\Pr_{R_{\mathrm{alt}}(t)}[f_0\ne f_1]$,
--   $$\Pr[R_{\mathrm{alt}}(t)\text{ wins}]=\frac12+\frac{\delta_t}4\ \ge\ \frac12+\frac{|p_0(t)-p_1(t)|}4 .$$
--
--   On a flag mismatch both outputs are copies of one challenge, which Algorithm 4.6 exploits; a gap between the two acceptance probabilities forces mismatches.
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
--   - reading: D_p applies U_p† to the register and discards the ancillary qubits, for a unitary U_p implementing E_p → D_p(σ) = E_p†σE_p + tr((I − E_pE_p†)σ)|0⟩⟨0|; reason: the paper's D_p presupposes a qubit register and depends on the choice of U_p; only its property D_p(E_pρE_p†) = ρ is used, which this CPTP map has
--   - encoding: game index j ∈ {1, 2}, challenge 1 to P0 and challenge 2 to P1 → j : Fin 2 (0-based), qubit 0 encoded by E0 for P0 and qubit 1 by E1 for P1; reason: renaming of indices
--   - encoding: pure states |ψ⟩ → density matrices |ψ⟩⟨ψ| (vectors ι → ℂ with the standard inner product); reason: global phase is not observable; same instances
--   - encoding: choose orthonormal states e_{p,0}, e_{p,1} ∈ S_p → hypotheses IsOrthonormalPair e_p and e_p a ∈ S_p on given vectors; reason: the choice is arbitrary; such vectors exist because dim S_p ≥ 2
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Lemma 4.12, p.24

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_winProb
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_PerfectlySecure
import Definitions.Def_QFairEx_Protocol_pAcc
import Definitions.Def_QFairEx_Protocol_ralt

namespace QFairEx

/-- **Lemma 4.12 (advantage from an acceptance gap).** Chung, Lee, Raizes, Thyagarajan,
*Quantum Fair Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883…),
Lemma 4.12, p.24: "Suppose the protocol is perfectly secure against fail-stop adversaries in
the communication model of Definition 4.1. For every cut t, let δt := Pr_{Ralt(t)}[f0 ≠ f1].
Then Pr[Ralt(t) wins] = 1/2 + δt/4 ≥ 1/2 + |p0(t) − p1(t)|/4."

For a valid protocol perfectly secure for `(S0, S1)`, orthonormal encodings into `S0`, `S1`,
and every cut `t ≤ T`. -/
theorem lemma_4_12 {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (S0 : Submodule ℂ (ι0 → ℂ)) (S1 : Submodule ℂ (ι1 → ℂ))
    (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (he0 : IsOrthonormalPair e0) (he0S : ∀ a, e0 a ∈ S0)
    (he1 : IsOrthonormalPair e1) (he1S : ∀ a, e1 a ∈ S1)
    (P : Protocol ι0 ι1) (hP : P.IsValid) (hsec : PerfectlySecure P S0 S1)
    (t : ℕ) (ht : t ≤ P.T) :
    winProb (P.ralt e0 e1 t) = 1 / 2 + P.deltaFlags e0 e1 t / 4 ∧
      1 / 2 + |P.pAcc e0 e1 0 t - P.pAcc e0 e1 1 t| / 4 ≤ 1 / 2 + P.deltaFlags e0 e1 t / 4 := by sorry

end QFairEx
