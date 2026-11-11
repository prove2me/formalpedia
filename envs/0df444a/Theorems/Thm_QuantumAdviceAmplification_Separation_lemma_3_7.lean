-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_lemma_3_7
-- name    : QuantumAdviceAmplification.Separation.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:41.225291+00:00
-- url     : https://prove2.me/theorems/90c6c09c-8a57-409d-8027-d35f48f3fc50
-- title:
--   Lemma 3.7 — Protocol accuracy and actual decoding time
-- statement:
--   For Protocol 1, suppose $2/\ell\le\varepsilon\le1/2$ and
--   $$\frac d\ell\ge1-H(\varepsilon-2/\ell)+\frac{3\log_2\ell}{\ell}.$$
--   Then $\varepsilon^*(\ell,d)\le\varepsilon$, so the protocol has worst-message, worst-query error at most $\varepsilon$.
--
--   There is also one absolute constant $c_{\rm dec}\ge1$ for implementations taking at most $c_{\rm dec}(d+w^2)$ actual tape steps when all relevant indices and parameters fit in $w$ bits. Both hard-wired parameters and one uniform implementation receiving the two $w$-bit parameters are included.
--
--   This combines the protocol's full accuracy guarantee with its computational cost.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
--   - encoding: w bounds the bit lengths of the query, code positions, ell and d; ell,d may be supplied as w-bit integers → B*ell<=2^w for the logarithmic bound, strict bounds below 2^w on the actual query, code positions and parameters, and three equal-width fields for supplied ell,d,query; both implementation modes count transitions; reason: makes the bit-length and input-representation conventions explicit and retains a single absolute implementation constant
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.11, Lemma 3.7

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem lemma_3_7 :
    (∀ (S : BlockShape) (B : ℕ), 0 < B → ∀ ε : ℝ,
      2 / (S.ell : ℝ) ≤ ε → ε ≤ 1 / 2 →
      1 - H (ε - 2 / (S.ell : ℝ)) + 3 * log₂ S.ell / S.ell ≤ (S.d : ℝ) / S.ell →
      epsilonStar S ≤ ε ∧ IsRAC (protocolCode S B) ε) ∧
    ∃ cdec : ℝ, 1 ≤ cdec ∧ ProtocolImplementations cdec := by sorry

end QuantumAdviceAmplification.Separation
