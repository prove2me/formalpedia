-- Prove2me | Theorems.Thm_QFairEx_lemma_4_9
-- name    : QFairEx.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:19.183776+00:00
-- url     : https://prove2.me/theorems/41f0ed7a-9bc8-47b8-8f89-d356fa57c0fa
-- title:
--   Lemma 4.9 — endpoint probabilities $p_0(0)=p_1(0)=0$, $p_0(T)=p_1(T)=1$
-- statement:
--   Let a valid protocol be perfectly secure against fail-stop adversaries for accepting subspaces $S_0,S_1$, and let $e_{p,0},e_{p,1}\in S_p$ be orthonormal ($p=0,1$), defining the encodings $E_p$. Then the acceptance probabilities of the stopping executions satisfy
--   $$p_0(0)=p_1(0)=0,\qquad p_0(T)=p_1(T)=1.$$
--
--   At cut $0$ the honest party learns nothing about the other input, so exact-state resilience forbids acceptance; at cut $T$ perfect completeness forces acceptance.
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
--   - encoding: choose orthonormal states e_{p,0}, e_{p,1} ∈ S_p → hypotheses IsOrthonormalPair e_p and e_p a ∈ S_p on given vectors; reason: the choice is arbitrary; such vectors exist because dim S_p ≥ 2
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Lemma 4.9, p.23

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_Protocol
import Definitions.Def_QFairEx_Protocol_IsValid
import Definitions.Def_QFairEx_PerfectlySecure
import Definitions.Def_QFairEx_Protocol_pAcc

namespace QFairEx

/-- **Lemma 4.9 (endpoint probabilities).** Chung, Lee, Raizes, Thyagarajan, *Quantum Fair
Exchange*, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883…), Lemma 4.9, p.23:
"Under perfect security against fail-stop adversaries, p0(0) = p1(0) = 0, p0(T) = p1(T) = 1."

For a valid protocol that is perfectly secure for `(S0, S1)` and orthonormal encodings
`e0 0, e0 1 ∈ S0`, `e1 0, e1 1 ∈ S1` (§4.2.2, p.22), the acceptance probabilities of the
stopping executions satisfy `p₀(0) = p₁(0) = 0` and `p₀(T) = p₁(T) = 1`. -/
theorem lemma_4_9 {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] [DecidableEq ι0] [DecidableEq ι1]
    (S0 : Submodule ℂ (ι0 → ℂ)) (S1 : Submodule ℂ (ι1 → ℂ))
    (e0 : Fin 2 → ι0 → ℂ) (e1 : Fin 2 → ι1 → ℂ)
    (he0 : IsOrthonormalPair e0) (he0S : ∀ a, e0 a ∈ S0)
    (he1 : IsOrthonormalPair e1) (he1S : ∀ a, e1 a ∈ S1)
    (P : Protocol ι0 ι1) (hP : P.IsValid) (hsec : PerfectlySecure P S0 S1) :
    P.pAcc e0 e1 0 0 = 0 ∧ P.pAcc e0 e1 1 0 = 0 ∧
      P.pAcc e0 e1 0 P.T = 1 ∧ P.pAcc e0 e1 1 P.T = 1 := by sorry

end QFairEx
