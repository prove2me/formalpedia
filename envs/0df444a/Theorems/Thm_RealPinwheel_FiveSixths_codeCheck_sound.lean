-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_codeCheck_sound
-- name    : RealPinwheel.FiveSixths.codeCheck_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:11:43.169955+00:00
-- url     : https://prove2.me/theorems/8d9ac148-65e2-4f9a-ab40-ca43bd3ca2d2
-- title:
--   Checked compact cycles dominate their density boxes
-- statement:
--   Let $c$ be a compact cycle code for $n>0$ task labels and suppose its exact integer cycle check succeeds. For positive real periods $a_i$, suppose the density vector $(1/a_i)$ belongs to the rational box encoded by $c$, respecting its strict and inclusive endpoints. Then repetition of the decoded cycle yields a valid schedule $S$ with a positive integer period $L$ satisfying
--
--   $$L=|c|,\qquad S(t+L)=S(t)\quad(t\ge0).$$
--
--   Here $|c|$ denotes the decoded word length. This bridges exact finite certificate checks to schedulability for arbitrary real periods; coverage of the density domain is a separate obligation.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 3, dominance boxes and equation (2), printed pp. 7–8 (PDF pp. 8–9), Section 4 Table 1, printed p. 10 (PDF p. 11).

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.codeCheck_sound {n : ℕ} (hn : 0 < n) (c : CycleCode)
    (hcheck : codeCheck n hn c = true) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : codeBox c (fun i => 1 / a i)) :
    ∃ (L : ℕ) (S : ℕ → Fin n),
      L = (codeWord n hn c).size ∧ Periodic S L ∧ Valid a S := by sorry
