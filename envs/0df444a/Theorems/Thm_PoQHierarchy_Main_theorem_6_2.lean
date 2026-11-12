-- Prove2me | Theorems.Thm_PoQHierarchy_Main_theorem_6_2
-- name    : PoQHierarchy.Main.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:55:01.271422+00:00
-- url     : https://prove2.me/theorems/380d4d3c-de66-4113-9e3f-f70a1037a455
-- title:
--   Theorem 6.2 — hierarchy of proofs of quantumness: $\mathsf{PPT}^{1\text{-intQPT}}\subsetneq\mathsf{PPT}^{2\text{-intQPT}}\subsetneq\cdots\subsetneq\mathsf{PPT}^{\infty\text{-intQPT}}=\mathsf{QPT}$
-- statement:
--   Assume the existence of a post-quantum secure QFHE scheme. Then the strict hierarchy
--   $$\mathsf{PPT}^{1\text{-intQPT}}\subsetneq\mathsf{PPT}^{2\text{-intQPT}}\subsetneq\mathsf{PPT}^{3\text{-intQPT}}\subsetneq\cdots\subsetneq\mathsf{PPT}^{\infty\text{-intQPT}}=\mathsf{QPT}$$
--   holds, in the following sense. For every post-quantum secure QFHE scheme and every $k\ge1$, with $n=k+1$:
--
--   1. $\mathsf{PPT}^{k\text{-intQPT}}\subseteq\mathsf{PPT}^{(k+1)\text{-intQPT}}\subseteq\mathsf{PPT}^{\infty\text{-intQPT}}=\mathsf{QPT}$;
--   2. there exist an $n$-player nonlocal game $G$ and constants $s<c$ such that the $n$-round fully encrypted compiled game $G_{\mathrm{all\text{-}comp}}$ separates $k$ from $k+1$ invocations:
--      - every prover $P\in\mathsf{PPT}^{k\text{-intQPT}}$ has a negligible $\mu_P$ with $\Pr[P\text{ wins }G^\lambda_{\mathrm{all\text{-}comp}}]\le s+\mu_P(\lambda)$ for all $\lambda$;
--      - some prover $P'\in\mathsf{PPT}^{(k+1)\text{-intQPT}}$ has a negligible $\mu'$ with $\Pr[P'\text{ wins }G^\lambda_{\mathrm{all\text{-}comp}}]\ge c-\mu'(\lambda)$ for all $\lambda$.
--
--   So each additional invocation of the quantum device yields a constant advantage in a classically specified interactive game. The constants $s,c$ depend only on $k$; the negligible function in the soundness clause depends on the prover. The first separation $\mathsf{PPT}^{0\text{-intQPT}}\subsetneq\mathsf{PPT}^{1\text{-intQPT}}$ is not claimed (the paper leaves it open).
--
--   Differences from the source:
--   - reading: PPT^{k-intQPT} ⊊ PPT^{(k+1)-intQPT} (strict hierarchy) → the inclusions as sets of machines, plus a separation of winning probabilities by constants s < c in the (k+1)-round game G_all-comp; reason: pp.4 and 25 define the separation "through their achievable winning probabilities"; Theorem 1.1 and the proof (pp.42–43) state the constant gap; literal strictness of machine sets would be trivial
--   - generalization: assume a post-quantum secure QFHE scheme exists → for every post-quantum secure QFHE scheme, its compiled game separates; reason: implies the conditional statement
--   - encoding: PPT^{∞-intQPT} = QPT → QPT is defined as PPTk ⊤, and the equation holds by definition; reason: p.25 presents QPT as this special case of Definition 4.1
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
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.42, Theorem 6.2 (proof pp.42–43); Theorem 1.1 (p.6, informal); pp.4, 25 (separation through winning probabilities); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Compiled

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-- Theorem 6.2 (Hierarchy of Proofs of Quantumness), p.42: assuming a post-quantum secure QFHE
scheme, `PPT^{1-intQPT} ⊊ PPT^{2-intQPT} ⊊ ⋯ ⊊ PPT^{∞-intQPT} = QPT`. For every secure scheme and
every `k ≥ 1`, with `n = k + 1`:
1. `PPT^{k-intQPT} ⊆ PPT^{(k+1)-intQPT} ⊆ PPT^{∞-intQPT} = QPT`;
2. there are an `n`-player nonlocal game `G` and constants `s < c` such that every
   `P ∈ PPT^{k-intQPT}` wins the `n`-round game `G_all-comp` with probability at most
   `s + μ_P(λ)` for a negligible `μ_P`, while some `P' ∈ PPT^{(k+1)-intQPT}` wins it with
   probability at least `c - μ'(λ)` for a negligible `μ'`. -/
theorem theorem_6_2 (Sch : QFHE) (hSch : Sch.IsSecureQFHE) (k : ℕ) (hk : 1 ≤ k) :
    (PPTk (k : ℕ∞) ⊆ PPTk ((k + 1 : ℕ) : ℕ∞) ∧ PPTk ((k + 1 : ℕ) : ℕ∞) ⊆ PPTk ⊤ ∧
      QPT = PPTk ⊤) ∧
    ∃ G : NonlocalGame (k + 1), G.IsValid ∧ ∃ s c : ℝ, s < c ∧
      (∀ P ∈ PPTk (k : ℕ∞), ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧
        ∀ lam : ℕ, winAllComp Sch G P lam ≤ s + μ lam) ∧
      (∃ P' ∈ PPTk ((k + 1 : ℕ) : ℕ∞), ∃ μ' : ℕ → ℝ, CompNonlocal.Negligible μ' ∧
        ∀ lam : ℕ, c - μ' lam ≤ winAllComp Sch G P' lam) := by sorry

end PoQHierarchy.Main
