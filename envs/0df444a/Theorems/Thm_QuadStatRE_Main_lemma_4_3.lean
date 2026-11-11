-- Prove2me | Theorems.Thm_QuadStatRE_Main_lemma_4_3
-- name    : QuadStatRE.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:46:52.572492+00:00
-- url     : https://prove2.me/theorems/a150ee55-9aaf-4903-b003-ff37e3faf742
-- title:
--   Lemma 4.3 — one RM step: correctness error ≤ 15δ, ZPP failure ≤ 1 − (1 − δ)^15 ≤ 15δ, degree ≤ 2 preserved
-- statement:
--   Let $E$ be an encoding of $f(x,y,z,w)=xyz+w$ (an encoder given by an $\mathbb F_2$-polynomial description, and a decoder) and let $E'$ be its amplification by Construction 3. Let $\delta\in\mathbb R$.
--
--   1. If $E$ has correctness error at most $\delta$ (for every input), then $E'$ has correctness error at most $15\delta$.
--   2. If $E$ has a ZPP-decoder with failure probability at most $\delta$, then $E'$ has a ZPP-decoder with failure probability at most
--   $$1-(1-\delta)^{15}\le15\delta .$$
--   3. If every output bit of $E$ has total degree at most two in its input and random bits, so has every output bit of $E'$ (affine substitution preserves total degree at most two).
--
--   The lemma bounds the price in correctness of one privacy-amplification step; iterating it gives the correctness of $\mathrm{Enc}_{r,t}$.
--
--   **Formalization Note.** The amplified decoder outputs $\bot$ if some child decoder does and otherwise the XOR of the child values. In the ordinary case $\bot$ counts as a decoding error.
--
--   Differences from the source:
--
--   - encoding: E a randomized encoding of f → Enc4: an encoder given by an F₂-polynomial description F₂⁴ × F₂^ρ → F₂^m with a decoder; reason: every map between bit strings is a polynomial map over F₂, so no encoding is lost; the description is what the degree clause is about
--   - reading: 1 − (1 − δ)^15 ≤ 15δ, δ a failure probability → the inequality is asserted for δ ≤ 1 (δ ≥ 0 follows from the hypothesis); reason: δ bounds a probability; for δ > 2 the inequality is false (δ = 3: 32769 > 45)
--   - encoding: the amplification of E (Construction 3) → amplify E: tape = A (12 bits), ω (14 bits; w_u = ω_u at the first 14 positions, the last w + Σω), the fifteen child tapes; description by affine substitution; reason: the 26 sharing bits of p. 22 laid out explicitly
--   - encoding: positions I = F₂⁴ ∖ {0} → Fin 15, position k the vector of binary digits of k + 1; reason: an enumeration of I; each nonzero vector occurs once
--   - encoding: bits {0,1} and F₂ → ZMod 2; reason: the same field
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 23, Lemma 4.3

import Mathlib
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadStatRE_Main_LeakyEncoding
import Definitions.Def_QuadStatRE_Main_RMSharing
open QuadraticRE

namespace QuadStatRE.Main

/-- Lemma 4.3 (One-step correctness), p. 23: (1) if `E` has correctness error at most `δ`, its
amplification has correctness error at most `15δ`; (2) if `E` has a ZPP-decoder with failure
probability at most `δ`, its amplification has a ZPP-decoder with failure probability at most
`1 − (1 − δ)^15`, and `1 − (1 − δ)^15 ≤ 15δ`; (3) the amplification preserves total degree at most
two. -/
theorem lemma_4_3 (E : Enc4) (δ : ℝ) :
    (IsCorrect targetF E.desc.eval δ E.dec →
      IsCorrect targetF (amplify E).desc.eval (15 * δ) (amplify E).dec) ∧
    (IsZPPDecoder targetF E.desc.eval δ E.dec →
      IsZPPDecoder targetF (amplify E).desc.eval (1 - (1 - δ) ^ 15) (amplify E).dec ∧
        (δ ≤ 1 → 1 - (1 - δ) ^ 15 ≤ 15 * δ)) ∧
    (E.desc.DegLE 2 → (amplify E).desc.DegLE 2) := by sorry

end QuadStatRE.Main
