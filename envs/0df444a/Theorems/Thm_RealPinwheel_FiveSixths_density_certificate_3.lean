-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_3
-- name    : RealPinwheel.FiveSixths.density_certificate_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:15:42.839267+00:00
-- url     : https://prove2.me/theorems/df527aaa-2ab8-4570-b738-f318d51dc5c4
-- title:
--   Dimension 3: five-sixths certificate with period at most 12
-- statement:
--   Let $A$ be an ordered real-period instance with exactly 3 distinct task labels, periods at least one, and density at most $5/6$. It has a valid periodic schedule with positive integer period $L$ satisfying
--
--   $$L\le12.$$
--
--   This is the dimension-3 certificate assertion used for Lemma 5, with the maximum word length from Table 1 retained. Equal numerical periods still represent different tasks. Validity quantifies over every window and every positive multiplicity.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 4, Lemma 5 and Table 1, printed p. 10 (PDF p. 11); family W_3, data https://github.com/grzegorz-gutowski/pinwheel_scheduling/blob/c133a7159fc26d41612111a412ee3e57c720414d/packing_plans/proof_5_6/D3.txt

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.density_certificate_3 (A : Instance 3) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 3), 0 < L ∧ L ≤ 12 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
