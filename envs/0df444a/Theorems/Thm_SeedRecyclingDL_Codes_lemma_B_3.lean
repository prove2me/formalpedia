-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_B_3
-- name    : SeedRecyclingDL.Codes.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:26.797187+00:00
-- url     : https://prove2.me/theorems/75413571-ee24-48e7-8930-3855c79875f2
-- title:
--   Lemma B.3 — Correctness and termination of the generic decoder (corrected: effective suffix search)
-- statement:
--   Under all the hypotheses of Lemma 3.2 and the source's total listing and tag inversion assumptions, every valid output of $c=\operatorname{Enc}(x,\sigma,\tau)$ has $c$ as its unique passing candidate in Step 1. Procedure B.2 then outputs exactly $(x,\sigma,\tau)$. On every finite input it halts, invokes each bad-list computation at most once, and returns a message of length $m+2b-2$ or failure.
--
--   For general channels satisfying the complete uniform algorithmic assumptions of Theorem 3.3, the corresponding greedy construction has a uniform deterministic decoder with
--   $$\operatorname{time}(n,y)\le K(n+|y|+1)^d.$$
--   The generic polynomial-time construction uses an effective suffix search rather than attempting to execute a ceiling of arbitrary real constants. The identity-channel counterexample and preservation of the source bounds are recorded in MODERATION_NOTES.md. This correction affects only that general implementation clause; DL parameters and the headline result are unchanged.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: asymptotic deterministic bit complexity → finite programs with actual charged RAM executions and uniform positive constants before lengths and inputs; reason: the fixed instruction semantics generates costs; a function with an assigned runtime is not accepted
--   - reading: bit operations on a RAM without a prescribed tape layout → helper routines use length and packed-value natural cells, while main and generic decoders receive raw bit streams; reason: each cell read and output is charged by bit length; raw decoder streams permit bounded inspection of arbitrarily long invalid inputs
--   - correction: the final runtime clause uses the proof choice N=h+ceil(c log2(2h)+log2 C) for arbitrary real c,C → choose the first N between h and floor(n/2) whose actual greedy table has at least 2^h entries; reason: for the identity channel, L=1, C=1 and a fixed noncomputable real c in (0,1), decoding the all-zero word under the source formula reveals ceil(c log2(2h)) and hence c; the effective search retains all hypotheses and the original upper bound
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma B.3, printed p. 17 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Interfaces

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

/-- The general polynomial-time clause uses an effective greedy suffix search.
The source ceiling involving arbitrary real degree bounds need not be computable;
MODERATION_NOTES.md records the identity-channel counterexample and the correction.
The generic correctness/termination clauses retain all source hypotheses. -/
theorem lemma_B_3 :
    (∀ (F : Type) [Field F] [Fintype F] (P : FieldPresentation F), P.p = 2 →
      ∀ (m N L r : ℕ) (E : Channel) (R : Word → Word → Prop) (Γ : Competitors),
        ContainsInput E → Splittable E m N R → ValidCompetitors m L Γ →
        (∀ x : Word, x.length = m → payloadCompetitors E m N x ⊆ ↑(Γ x)) →
        ValidParameters m L P.k r → ∀ A : Word → Word, TagCode (2 * P.k + r) N R A →
        ∀ (preimages : Word → List Word) (inverse : Word → Option Word),
          ListingAlgorithms (m + N) m E Γ A (2 * P.k + r) N preimages inverse →
          (∀ x sigma tau y : Word, x.length = m → sigma.length = P.k - 1 → tau.length = P.k - 1 →
            y ∈ E (m + N) (encode P m r Γ A x sigma tau) →
            firstCandidate P m N r preimages inverse y = some (encode P m r Γ A x sigma tau) ∧
            (∀ z : Word, z ∈ preimages y → passesCandidate P m N r inverse z = true →
              z = encode P m r Γ A x sigma tau) ∧
            procedureB2 P m N r Γ preimages inverse y = some (x ++ sigma ++ tau)) ∧
          (∀ y : Word,
            (badListCalls P m N r Γ preimages inverse y).1 ≤ 1 ∧
            (badListCalls P m N r Γ preimages inverse y).2 ≤ 1 ∧
            (∀ mu : Word, procedureB2 P m N r Γ preimages inverse y = some mu →
              mu.length = m + 2 * P.k - 2)) ∧
          (∃ decoder : Program, ∀ y : Word,
            Halts decoder (m + N) (y.map Fin.val)
              ((procedureB2 P m N r Γ preimages inverse y).map (List.map Fin.val)))) ∧
    (∀ G : GeneralChannelData, GeneralChannelAssumptions G →
      ∃ (data : ℕ → FieldData) (decoder : Program) (K : ℝ) (d n₀ : ℕ), 0 < K ∧
        ∀ n : ℕ, n₀ ≤ n →
          (data n).presentation.p = 2 ∧ (data n).presentation.k = generalFieldWidth G n ∧
          ∀ y : Word, Executes decoder n (y.map Fin.val)
            ((generalDecoder data G n y).map (List.map Fin.val)) (K * (n + y.length + 1 : ℕ) ^ d))
    := by sorry

end SeedRecyclingDL.Codes
