-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_lemma_3_2
-- name    : SeedRecyclingDL.Codes.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:31.9613+00:00
-- url     : https://prove2.me/theorems/4f7765c4-fd42-48ce-9ca8-1a51a85c899c
-- title:
--   Lemma 3.2 — From tags to codes
-- statement:
--   Let $n=m+N$, let the channel be $(m,N,R_N)$-splittable, and let $\widetilde\Gamma(x)$ contain the exact payload competitors, exclude $x$, and have at most $L$ elements. For source-valid $b,r$, put $h=2b+r$, and let $A$ be an injective tag code separating $R_N$. Then
--   $$\operatorname{Enc}(x,\sigma,\tau)=x\Vert A(\operatorname{Tag}(x,\sigma,\tau))$$
--   is injective, and its image $C$ corrects the channel. Its exact redundancy is
--   $$n-\log_2|C|=(r+2)+(N-h).$$
--   With $r=\lceil\log_2(2L)\rceil$ it is at most $\log_2L+4+(N-h)$. The equality uses signed real subtraction, without assuming an unproved natural subtraction identity. This is the generic transfer from tags to codes.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - encoding: the binary polynomial-basis field of order 2^b → a published finite-field Presentation with characteristic parameter 2, degree b, and its coefficient coordinates; reason: the quotient isomorphism and reconstruction certify the same field; coordinate order is constant coefficient first, and integer value is most significant bit first
--   - encoding: the signed redundancy contribution N-h → real subtraction of the two natural lengths; reason: no potentially truncated natural subtraction is used in the equality
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Lemma 3.2, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem lemma_3_2 {F : Type} [Field F] [Fintype F]
    (P : FieldPresentation F) (hp : P.p = 2) (m N L r : ℕ)
    (E : Channel) (hE : ContainsInput E) (R : Word → Word → Prop)
    (hsplit : Splittable E m N R) (Γ : Competitors)
    (hΓ : ValidCompetitors m L Γ)
    (hcontain : ∀ x : Word, x.length = m → payloadCompetitors E m N x ⊆ ↑(Γ x))
    (hpar : ValidParameters m L P.k r) (A : Word → Word)
    (hA : TagCode (2 * P.k + r) N R A) :
    (∀ x sigma tau x' sigma' tau' : Word,
      x.length = m → x'.length = m → sigma.length = P.k - 1 → tau.length = P.k - 1 →
      sigma'.length = P.k - 1 → tau'.length = P.k - 1 →
      encode P m r Γ A x sigma tau = encode P m r Γ A x' sigma' tau' →
      x = x' ∧ sigma = sigma' ∧ tau = tau') ∧
    Corrects E (m + N) (codeImage P m r Γ A) ∧
    redundancy (m + N) (codeImage P m r Γ A) =
      (r + 2 : ℝ) + ((N : ℝ) - (2 * P.k + r : ℕ)) ∧
    (r = EditMulticoloring.Code.ceilLog 2 (2 * L) →
      redundancy (m + N) (codeImage P m r Γ A) ≤
        log₂ L + 4 + ((N : ℝ) - (2 * P.k + r : ℕ))) := by sorry

end SeedRecyclingDL.Codes
