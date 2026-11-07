-- Prove2me | Theorems.Thm_StretchDepth_no_repeat_normal_form
-- name    : StretchDepth.no_repeat_normal_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:54.264753+00:00
-- url     : https://prove2.me/theorems/89f02147-0b06-4909-a6a7-4a84ad76208a
-- title:
--   Definition 1 — every construction has a no-repeat form
-- statement:
--   Let $H$ be a $(q,d)$-construction. Then there is a $(q,d)$-construction $H'$ in which no input is queried more than once in any execution, with
--   $$
--   H'^G(x)=H^G(x)\qquad\text{for every oracle }G\text{ and every }x.
--   $$
--   This removes repeated queries, so the critical-query counting of Lemma 1 applies to every construction.
--
--   Differences from the source:
--   - reading: "Without loss of generality, no input is queried more than once" → existence of an equivalent construction with the same q and d and no repeated query; reason: this is what "without loss of generality" asserts, and Lemma 1 needs exactly this
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 1, p.13

import Definitions.Def_StretchDepth_IsConstruction

namespace StretchDepth

/-- **Definition 1, no-repeat normal form.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 1, p.13: "Without loss of generality, no input is queried more than once in an
execution of HG(x)."

**Formalization Note.** Every `(q, d)`-construction has an equivalent one with no repeated query,
with the same output on every input and every oracle. -/
theorem no_repeat_normal_form {n N m M : ℕ} (H : Bits m → RoundTree n N M) (q d : ℕ)
    (hH : IsConstruction H q d) :
    ∃ H' : Bits m → RoundTree n N M, IsConstruction H' q d ∧ NoRepeat H' ∧
      ∀ (G : Bits n → Bits N) (x : Bits m), run G (H' x) = run G (H x) := by sorry

end StretchDepth
