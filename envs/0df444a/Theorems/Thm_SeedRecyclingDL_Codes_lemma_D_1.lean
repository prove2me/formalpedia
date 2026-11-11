-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_D_1
-- name    : SeedRecyclingDL.Codes.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:51.922206+00:00
-- url     : https://prove2.me/theorems/b14e7961-f952-4866-ac16-d9293e128d50
-- title:
--   Lemma D.1 — Bootstrapping
-- statement:
--   Let a channel family contain each input. For all $\ell\ge\ell_0\ge1$, assume actual correct codes, injective encoders on $M(\ell)$ bits, and decoders that halt on every input and recover every valid channel output. Uniform programs compute $M$, perform setup, and run the encoder/decoder within nondecreasing bounds $\theta,P,\operatorname{Time}$, with nondecreasing $R$ satisfying $\ell-M(\ell)\le R(\ell)\le\ell/2$.
--
--   For every $h\ge\ell_0$, the actual least admissible length $N_h$ and padded encoder satisfy
--   $$h<N_h\le2h,\qquad N_h-h\le1+R(2h).$$
--   The map $A_h$ is injective with pairwise nonconfusable images. Its inverse tests padding and re-encodes. Uniform finite programs find $N_h$ and set up $A_h$ in $O(h\theta(2h)+P(2h))$ time; evaluation, membership, and inversion each take $O(\operatorname{Time}(2h)+h)$. No DL restriction is imposed. The underlying family is an input hypothesis here, while correctness of the derived tag code is a conclusion.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - encoding: channel lengths indexed by positive integers → ell0 is explicitly at least 1; reason: this is the domain of the source family
--   - generalization: decoder results are ordinarily M(ell)-bit messages or failure → invalid inputs may also yield malformed words, which the membership routine rejects by a length check; reason: every source decoder is included and correctness on valid outputs is unchanged
--   - generalization: Dec_ell halts on every input and runs in time Time(ell) → Dec_ell's program halts with output Dec_ell(y) on every finite input, and the Time(ell) bound is required only on inputs of length ell; reason: a decoder meeting Time(ell) on every input is an instance, and the bootstrapped tag code only calls Dec on words of length N_h
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma D.1, printed p. 22 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Interfaces

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_D_1 (E : Channel) (hE : ContainsInput E) (ell₀ : ℕ) (hell : 1 ≤ ell₀)
    (M : ℕ → ℕ) (C : ℕ → Set Word) (Enc : ℕ → Word → Word)
    (Dec : ℕ → Word → Option Word) (cells : ℕ → List ℕ) (family : FamilyPrograms)
    (theta P Time R : ℕ → ℝ)
    (htheta : Monotone theta) (hP : Monotone P) (hTime : Monotone Time) (hR : Monotone R)
    (hfamily : ∀ ell : ℕ, ell₀ ≤ ell → CorrectFamily E M C Enc Dec ell ∧
      FamilyAlgorithms family ell M Enc Dec cells theta P Time ∧
      (ell : ℝ) - M ell ≤ R ell ∧ R ell ≤ (ell : ℝ) / 2) :
    ∃ (progs : Programs) (K : ℝ), 0 < K ∧ ∀ h : ℕ, ell₀ ≤ h →
      let N := bootstrapLength M h
      h < N ∧ N ≤ 2 * h ∧ (N : ℝ) - h ≤ 1 + R (2 * h) ∧
      (∀ T : Word, T.length = h → (bootstrapTag M Enc h T).length = N) ∧
      (∀ T T' : Word, T.length = h → T'.length = h →
        bootstrapTag M Enc h T = bootstrapTag M Enc h T' → T = T') ∧
      (∀ T T' : Word, T.length = h → T'.length = h → T ≠ T' →
        ¬ Confusable E N (bootstrapTag M Enc h T) (bootstrapTag M Enc h T')) ∧
      (∀ T u : Word, T.length = h → u.length = N →
        bootstrapInverse M Enc Dec h u = some T ↔ u = bootstrapTag M Enc h T) ∧
      ∃ saved : MachineState,
        SetupExecutes progs.setup h ([N, M N] ++ cells N) saved
          (K * ((h : ℝ) * theta (2 * h) + P (2 * h))) ∧
        (∀ T : Word, T.length = h →
          ResumedExecutes progs.encoder h saved (T.map Fin.val)
            (some ((bootstrapTag M Enc h T).map Fin.val)) (K * (Time (2 * h) + h))) ∧
        (∀ u : Word, u.length = N →
          ResumedExecutes progs.decoder h saved (u.map Fin.val)
            ((bootstrapInverse M Enc Dec h u).map (List.map Fin.val)) (K * (Time (2 * h) + h))) ∧
        (∀ u : Word, u.length = N →
          ResumedExecutes progs.payload h saved (u.map Fin.val)
            (some [if (bootstrapInverse M Enc Dec h u).isSome then 1 else 0])
            (K * (Time (2 * h) + h))) := by sorry

end SeedRecyclingDL.Codes
