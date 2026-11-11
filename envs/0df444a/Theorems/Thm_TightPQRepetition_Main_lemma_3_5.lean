-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_3_5
-- name    : TightPQRepetition.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:42:26.828265+00:00
-- url     : https://prove2.me/theorems/909e3cd1-101d-46ae-bc07-ade571751196
-- title:
--   Lemma 3.5 — the transformation preserves completeness and single-copy soundness
-- statement:
--   Let $V$ be an efficient verifier.
--
--   1. For every efficient scheme and every QPT prover $\widehat A$ against $\widehat V$ there is a QPT prover $A$ against $V$ with the same acceptance probability up to a negligible additive error.
--
--   2. For every scheme of Definition 2 and every QPT prover $P$ against $V$, honest or not, whose answers in each round have a length fixed in advance, there is a QPT prover $\widehat P$ against $\widehat V$ with the same acceptance probability up to a negligible additive error, and for all polynomially bounded $t\le k$,
--   $$\big|\Pr[\langle P^{\otimes k},V^{k,t}\rangle(1^\lambda)=1]-\Pr[\langle\widehat P^{\otimes k},\widehat V^{k,t}\rangle(1^\lambda)=1]\big|$$
--   is negligible.
--
--   3. The same holds for every scheme of Definition 1 and classical $P$, with $\widehat P$ classical (Remark 3.3).
--
--   Part 1 is the simulation giving soundness of $\widehat V$ from soundness of $V$; parts 2 and 3 give completeness, single and repeated, and the converse simulation. Soundness under repetition is not claimed (Remark 3.6).
--
--   Differences from the source:
--   - generalization: PPT verifier and encryption algorithms (uniform) → non-uniform families of polynomial-size Boolean circuits, with coins an explicit input and outputs of bounded, input-dependent length; reason: a uniform PPT algorithm gives such a family, so every source instance is covered; the source already takes all adversaries non-uniform (Remark 5.2)
--   - encoding: QPT prover with quantum advice → a family of `Strategy`: a pure advice state, one unitary circuit of one- and two-qubit gates per round, computational-basis measurement of answer wires, and a polynomial-size classical controller with a random tape; reason: purification costs polynomial overhead (PDF p. 22); the source fixes no gate set
--   - reading: the honest prover P̂ is fixed only in the proof of the lemma; step 2(b) of §3.3.1 says "some response" → there exists a QPT P̂, the same one for the single and repeated claims; reason: the lemma asserts completeness of the transformed protocol, witnessed by the prover of the proof
--   - reading: same soundness up to negligible error → two simulations: every QPT prover on one side has a QPT prover on the other side with acceptance probability within a negligible function; reason: this implies equality of the soundness errors, prover by prover, in the sense of Notation 1
--   - reading: FHE.Eval and QFHE.Eval take one ciphertext → they take a tuple of ciphertexts under one key and give one per output register; reason: the prover of the proof must join its state, the encrypted key and the query, and must return an answer ciphertext that the verifier decrypts alone; the one-ciphertext syntax is the tuple of length one
--   - generalization: completeness for the honest P, and the converse soundness simulation → one clause for every QPT P with quantum advice, honest or cheating; reason: the honest prover is one such P, and the converse soundness simulation is the same construction applied to a cheating P
--   - generalization: the scheme is a QFHE of Definition 2, or an FHE of Definition 1 for Remark 3.3 → any `EncScheme`: efficient classical Gen, Enc, Dec with semantic security, with no homomorphic evaluation or correctness required; reason: the verifier and the soundness proof use only these; `ClassicalFHE.toEncScheme` and `QFHE.toEncScheme` give the source's two cases
--   - reading: queries q_j of unspecified length → each q_j has a length depending only on λ and j; reason: the dummy Enc(0) of Algorithm 1 is prepared before the query is known, and semantic security needs |m₀| = |m₁|, so the length must be known in advance; a verifier reaches this form by padding
--   - reading: P̂ runs P under QFHE or FHE, with no condition on the length of its answers → parts 2 and 3 take P with answers of a length a(λ, j) fixed per round; reason: Definitions 1–2 encrypt messages m ∈ {0,1}^{poly(λ)} and evaluate circuits C : {0,1}^{poly(λ)} → {0,1}^{poly(λ)}, so the answers that P̂ computes under Eval have a length fixed per round; the other reading is false: for the one-round V that sends a random bit b and accepts iff |a| = b, the honest P has completeness 1, while under a scheme whose ciphertext length reveals the plaintext length P̂ would predict b, against semantic security. `IsQPT` alone admits varying lengths, so the restriction is stated
--   - reading: same soundness, under QFHE or FHE → for FHE the converse simulation is stated for classical P only; reason: a classical FHE cannot evaluate a quantum prover; Remark 3.3 uses FHE for a classical honest prover, and the proof of soundness cites the correctness of QFHE
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 3.5 and Remarks 3.3, 3.6, printed p. 11 / PDF p. 13

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Preprocess

namespace TightPQRepetition.Main

/-- Lemma 3.5 (printed p. 11, PDF p. 13). -/
theorem lemma_3_5 (V : Verifier) (hV : V.IsEfficient) :
    (∀ E : EncScheme, E.IsEfficient → ∀ Ahat : ℕ → Strategy, IsQPT Ahat →
      ∃ A : ℕ → Strategy, IsQPT A ∧ SameUpToNegl Ahat (hatV E V) A V) ∧
    (∀ Q : QFHE, Q.IsValid → ∀ P : ℕ → Strategy, IsQPT P →
      ∀ a : ℕ → ℕ → ℕ, (∀ lam, (P lam).HasAnswerLen (a lam)) →
      ∃ Phat : ℕ → Strategy, IsQPT Phat ∧ SameUpToNegl P V Phat (hatV Q.toEncScheme V) ∧
        ∀ k t : ℕ → ℕ, PolyBound k → PolyBound t → (∀ lam, t lam ≤ k lam) →
          SameUpToNegl (fun lam => (P lam).power (k lam)) (V.parallel k t)
            (fun lam => (Phat lam).power (k lam)) ((hatV Q.toEncScheme V).parallel k t)) ∧
    (∀ F : ClassicalFHE, F.IsValid → ∀ P : ℕ → Strategy, IsQPT P → (∀ lam, (P lam).IsClassical) →
      ∀ a : ℕ → ℕ → ℕ, (∀ lam, (P lam).HasAnswerLen (a lam)) →
      ∃ Phat : ℕ → Strategy, IsQPT Phat ∧ (∀ lam, (Phat lam).IsClassical) ∧
        SameUpToNegl P V Phat (hatV F.toEncScheme V) ∧
        ∀ k t : ℕ → ℕ, PolyBound k → PolyBound t → (∀ lam, t lam ≤ k lam) →
          SameUpToNegl (fun lam => (P lam).power (k lam)) (V.parallel k t)
            (fun lam => (Phat lam).power (k lam)) ((hatV F.toEncScheme V).parallel k t)) := by sorry

end TightPQRepetition.Main
