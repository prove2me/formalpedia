-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_2
-- name    : RealPinwheel.FiveSixths.density_certificate_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:15:29.585025+00:00
-- url     : https://prove2.me/theorems/345ee642-40a2-420d-9fd0-3ba3cecd8cb1
-- title:
--   Dimension 2: five-sixths certificate with period at most 6
-- statement:
--   Let $A$ be an ordered real-period instance with exactly 2 distinct task labels, periods at least one, and density at most $5/6$. It has a valid periodic schedule with positive integer period $L$ satisfying
--
--   $$L\le6.$$
--
--   This is the dimension-2 certificate assertion used for Lemma 5, with the maximum word length from Table 1 retained. Equal numerical periods still represent different tasks. Validity quantifies over every window and every positive multiplicity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 4, Lemma 5 and Table 1, printed p. 10 (PDF p. 11); family W_2, data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D2.txt

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.density_certificate_2 (A : Instance 2) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 2), 0 < L ∧ L ≤ 6 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
