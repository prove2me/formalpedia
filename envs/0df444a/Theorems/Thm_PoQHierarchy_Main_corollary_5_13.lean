-- Prove2me | Theorems.Thm_PoQHierarchy_Main_corollary_5_13
-- name    : PoQHierarchy.Main.corollary_5_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:55:04.522366+00:00
-- url     : https://prove2.me/theorems/9657f70a-5687-4ddb-97f8-077aa292bd63
-- title:
--   Corollary 5.13 — $\Pr[P\text{ wins }G_{\mathrm{all\text{-}comp}}]\le\max_{|I|=k}\omega_{qc\text{-}I}(G)+\varepsilon+\mathrm{negl}_\varepsilon(\lambda)$
-- statement:
--   Assume a post-quantum secure QFHE scheme. Let $G$ be an $n$-player nonlocal game with $n\ge2$, let $0\le k\le n$, and let $P\in\mathsf{PPT}^{k\text{-intQPT}}$ be an adaptive prover playing $G_{\mathrm{all\text{-}comp}}$. Then for every fixed $\varepsilon>0$ there exists a negligible function $\mathrm{negl}_\varepsilon$ such that for every $\lambda$
--   $$\Pr[P\text{ wins }G_{\mathrm{all\text{-}comp}}]\le\max_{I\subseteq[n],\ |I|=k}\omega_{qc\text{-}I}(G)+\varepsilon+\mathrm{negl}_\varepsilon(\lambda).$$
--
--   The negligible function depends on the prover and on $\varepsilon$. This is the paper's main soundness theorem (Theorem 1.2, informal): $k$ invocations buy at most what $k$ quantum players achieve in the nonlocal game.
--
--   Differences from the source:
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
--   - encoding: possibly infinite-dimensional Hilbert space H → any complex Hilbert space in Lean's lowest universe, with bounded operators; reason: the finitely many operators of a strategy generate a separable cyclic subspace, so no correlation is lost
--   - encoding: supremum winning probability → sSup in ℝ of the set of winning probabilities; reason: the set is bounded and nonempty whenever every O_i is nonempty; otherwise both sides have no strategy
--   - encoding: max over I ⊆ [n] with |I| = k → indexed supremum over {I : Finset (Fin n) // I.card = k}; reason: for k ≤ n the index set is finite and nonempty, so the supremum is the maximum
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.41, Corollary 5.13 (= Theorem 1.2, pp.8–9, informal); p.25 (0 ≤ k ≤ n); p.19 (n ≥ 2); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Compiled
import Definitions.Def_PoQHierarchy_Main_ICO

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Corollary 5.13, p.41: under a post-quantum secure QFHE scheme, for an adaptive prover
`P ∈ PPT^{k-intQPT}` (`k ≤ n`, p.25) playing `G_all-comp` and every fixed `ε > 0`, there is a
negligible `negl_ε` with
`Pr[P wins G_all-comp] ≤ max_{I ⊆ [n], |I| = k} ω_{qc-I}(G) + ε + negl_ε(λ)` for all `λ`. -/
theorem corollary_5_13 (Sch : QFHE) (hSch : Sch.IsSecureQFHE) {n : ℕ} (hn : 2 ≤ n)
    (G : NonlocalGame n) (hG : G.IsValid) (k : ℕ) (hk : k ≤ n) (P : IntMachine)
    (hP : P ∈ PPTk k) :
    ∀ ε : ℝ, 0 < ε → ∃ negl : ℕ → ℝ, CompNonlocal.Negligible negl ∧
      ∀ lam : ℕ, winAllComp Sch G P lam ≤
        (⨆ I : {I : Finset (Fin n) // I.card = k}, omegaQC G I.1) + ε + negl lam := by sorry

end PoQHierarchy.Main
