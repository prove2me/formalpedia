-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_7
-- name    : RealPinwheel.FiveSixths.density_certificate_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T03:15:38.844195+00:00
-- url     : https://prove2.me/theorems/56665a01-bfa5-4fa9-98c7-fd329dcc9a15
-- title:
--   Dimension 7: five-sixths certificate with period at most 352
-- statement:
--   Let $A$ be an ordered real-period instance with exactly 7 distinct task labels, periods at least one, and density at most $5/6$. It has a valid periodic schedule with positive integer period $L$ satisfying
--
--   $$L\le352.$$
--
--   This is the dimension-7 certificate assertion used for Lemma 5, with the maximum word length from Table 1 retained. Equal numerical periods still represent different tasks. Validity quantifies over every window and every positive multiplicity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 4, Lemma 5 and Table 1, printed p. 10 (PDF p. 11); family W_7, data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D7.txt

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.density_certificate_7 (A : Instance 7) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
