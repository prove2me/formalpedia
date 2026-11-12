-- Prove2me | Theorems.Thm_PoQHierarchy_Main_theorem_3_6
-- name    : PoQHierarchy.Main.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:54:46.390184+00:00
-- url     : https://prove2.me/theorems/41ae934a-b91e-4318-8359-21971791bba9
-- title:
--   Theorem 3.6 — KLVY quantum completeness and classical soundness [KLVY23, Thm 3.2], completeness also for $G_{\mathrm{all\text{-}comp}}$
-- statement:
--   Assume a post-quantum secure QFHE scheme, and let $G$ be an $n$-player nonlocal game with $n\ge2$. Then:
--
--   1. For every quantum strategy $S$ for $G$ given by circuits over $\{CX,H,T\}$, there is a prover $P'\in\mathsf{PPT}^{n\text{-intQPT}}$ that invokes its device exactly once in every round, and a negligible function, with
--   $$\Pr[P'\text{ wins }G_{\mathrm{comp}}]\ge\Pr[S\text{ wins }G]-\mathrm{negl}(\lambda)\quad\text{for all }\lambda;$$
--   the same holds for $G_{\mathrm{all\text{-}comp}}$ (with another such prover).
--   2. For every $\mathsf{PPT}$ prover $P_{cl}$ there is a negligible function with
--   $$\Pr[P_{cl}\text{ wins }G_{\mathrm{comp}}]\le\omega_c(G)+\mathrm{negl}(\lambda)\quad\text{for all }\lambda.$$
--
--   The paper cites this result from Kalai, Lombardi, Vaikuntanathan and Yang [KLVY23, Theorem 3.2] and notes (p.23) that it also holds for $G_{\mathrm{all\text{-}comp}}$. The proof of Theorem 6.2 uses clause 1 for $G_{\mathrm{all\text{-}comp}}$ with an honest prover in $\mathsf{PPT}^{n\text{-intQPT}}$ (p.43).
--
--   Differences from the source:
--   - reading: every quantum strategy S for G → every quantum strategy given by circuits over {CX, H, T} (state preparation, local circuits, measurement, classical answer map); reason: p.22: the compiler fixes a QHE for a class containing the circuits the players use, and Eval takes a circuit; a uniform prover cannot evaluate arbitrary complex amplitudes
--   - generalization: a quantum strategy S′ for G_comp → a prover in PPT^{n-intQPT}, non-adaptive with schedule 1^n, for G_comp and also for G_all-comp; reason: p.23 and p.43 use completeness in exactly this form; such a prover is in particular a quantum strategy for G_comp
--   - generalization: Gen(1^λ), Enc(sk,x), Eval(C,|Ψ⟩,ct), Dec(sk,ct) → every algorithm also receives 1^λ; reason: more schemes satisfy the hypothesis, so the statement implies the one for the printed syntax
--   - generalization: IND-CPA for any two messages x₀, x₁ → IND-CPA required only for messages of equal length; reason: a weaker hypothesis; the compiled games encrypt only fixed-length codes of one player's questions
--   - reading: "for every λ, any C, any |Ψ⟩, any x, any sk, any ct … negligible trace distance" → for every circuit C a negligible μ with TD ≤ μ(λ) for all λ, all |Ψ⟩_AB (B any number of qubits), x, sk and ct in the supports; reason: negligibility is in λ for a fixed circuit, uniformly over the state; the uniform-over-all-circuits reading is a stronger hypothesis
--   - encoding: Eval on quantum-output circuits and Dec on quantum ciphertexts → only classical-output circuits and classical ciphertexts are modelled; reason: no property of Definition 3.3 refers to quantum outputs, and the compiled games use only classical messages
--   - encoding: QPT algorithms (Eval, Dec, adversaries) → PPT^{∞-intQPT} machines; reason: p.25 states PPT^{∞-intQPT} = QPT
--   - encoding: PPT^{k-intQPT} algorithm (classical PPT machine with ≤ k device invocations) → efficient IntMachine: polynomial-time TM2 next-action function on (input, coins, history), polynomial bounds on coins, qubits, actions, action length; invocation limit on all histories consistent with its actions; reason: a PPT machine with oracle access is simulated by recomputation from its history in polynomial time; a machine counting its own queries realises the limit (p.25's ⊥ form)
--   - encoding: fixed binary encodings of questions and answers → one-hot codes of length |I_i| and |O_i|; reason: any fixed-length injective encoding serves; all questions of a player have codes of equal length
--   - encoding: the verifier of Fig. 4 → the winning probability as an explicit finite expectation over μ, Gen, Enc, the prover's execution and Dec; reason: the same probability space as the paper's experiment
--   - encoding: players [n] and finite question/answer sets I_i, O_i → Fin n, Fin (q i), Fin (o i); reason: every finite set is in bijection with some Fin m; values and correlations are unchanged
--   - encoding: Pr[a|x] = ⟨Ω|∏P|Ω⟩ (a real number) → the real part of the complex inner product in the winning probability; reason: the correlation is real, so the real part equals it
--   - encoding: ω_c(G), the supremum over classical strategies with shared randomness (p.20) → sSup in ℝ over strategies with finitely supported shared randomness and deterministic response functions; reason: the winning probability is linear in the shared randomness, so every classical strategy is a mixture of deterministic ones and the supremum is unchanged
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.23, Theorem 3.6 (citing [KLVY23, Theorem 3.2]); p.23 (G_all-comp); p.22 (the QHE class contains the players' circuits); p.43 (honest prover in PPT^{n-intQPT}, one invocation per round); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Compiled

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Theorem 3.6 (Quantum Completeness and Classical Soundness [KLVY23, Theorem 3.2]), p.23, with
clause 1 also for `G_all-comp` (p.23):
1. for every quantum strategy `S` for `G` given by circuits over the gate set, there are provers
   `P' ∈ PPT^{n-intQPT}` invoking the device once in every round with
   `Pr[P' wins G_comp] ≥ Pr[S wins G] - negl(λ)`, and likewise for `G_all-comp`;
2. for every `PPT` prover `P_cl`, `Pr[P_cl wins G_comp] ≤ ω_c(G) + negl(λ)`. -/
theorem theorem_3_6 (Sch : QFHE) (hSch : Sch.IsSecureQFHE) {n : ℕ} (hn : 2 ≤ n)
    (G : NonlocalGame n) (hG : G.IsValid) :
    (∀ S : CircStrategy G,
      (∃ P' ∈ PPTk n, P'.NonAdaptive (Schedule.allOnes n) ∧
        ∃ negl : ℕ → ℝ, CompNonlocal.Negligible negl ∧
          ∀ lam : ℕ, S.win - negl lam ≤ winComp Sch G P' lam) ∧
      (∃ P' ∈ PPTk n, P'.NonAdaptive (Schedule.allOnes n) ∧
        ∃ negl : ℕ → ℝ, CompNonlocal.Negligible negl ∧
          ∀ lam : ℕ, S.win - negl lam ≤ winAllComp Sch G P' lam)) ∧
    (∀ Pcl ∈ PPT, ∃ negl : ℕ → ℝ, CompNonlocal.Negligible negl ∧
      ∀ lam : ℕ, winComp Sch G Pcl lam ≤ omegaC G + negl lam) := by sorry

end PoQHierarchy.Main
