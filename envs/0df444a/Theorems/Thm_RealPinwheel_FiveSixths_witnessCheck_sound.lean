-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
-- name    : RealPinwheel.FiveSixths.witnessCheck_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:45:59.625935+00:00
-- url     : https://prove2.me/theorems/58df48a8-1763-4484-b592-31eada329e6e
-- title:
--   Exact discrepancy witnesses imply periodic validity
-- statement:
--   Let $w$ be a finite discrepancy witness for $n>0$ tasks, and suppose every arithmetic check succeeds. Let $a_i>0$ be arbitrary real periods whose reciprocal density vector belongs to the witness's annotated rational box, including the specified strict or inclusive endpoints. Then there exist a schedule $S$ and a positive integer period $L$ such that
--
--   $$L=|w|,\qquad S(t+L)=S(t)\quad(t\ge0),\qquad\operatorname{Valid}(a,S).$$
--
--   Here $|w|$ is the stored cycle length. The count recurrence identifies the finite tables with actual execution counts, and the discrepancy inequalities certify all residual windows. This provides an exact kernel-verifiable interface for the source's periodic certificate words without imposing rationality on the input periods.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 proof of equation (2), printed p. 8 (PDF p. 9), and Section 4 certificate verification, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf; finite-window discrepancy implementation of the same cyclic-window inequalities.

import Definitions.Def_RealPinwheel_FiveSixths_Witness
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.witnessCheck_sound {n : ℕ} (hn : 0 < n) (w : CycleWitness n)
    (hc : witnessCheck w = true) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : codeBox w.code (fun i => 1 / a i)) :
    ∃ (L : ℕ) (S : ℕ → Fin n), L = w.length ∧ Periodic S L ∧ Valid a S := by sorry
