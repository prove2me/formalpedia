-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_cycleCheck_sound
-- name    : RealPinwheel.FiveSixths.cycleCheck_sound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:03:47.561922+00:00
-- url     : https://prove2.me/theorems/71e4a8fd-dfdb-4076-85a0-bb350195d003
-- title:
--   Soundness of the finite-window cycle checker
-- statement:
--   Suppose a finite cycle passes the exact integer checks for positive rational density endpoints $p_i/q_i$, with either an open or closed upper face for each task. Let the positive task periods satisfy $a_i>q_i/p_i$ at an open face and $a_i\ge q_i/p_i$ at a closed face. Then repetition of the cycle gives a valid periodic schedule $S$ with period equal to its length $L$:
--
--   $$S(t+L)=S(t),\qquad \operatorname{Valid}(a,S).$$
--
--   Validity includes every positive multiplicity and every starting day. This theorem supplies the soundness interface for exact finite certificate verification; it makes no claim that any family covers a density domain.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 3, proof of equation (2), printed p. 8 (PDF p. 9), and Section 4, printed pp. 9–11 (PDF pp. 10–12).

import Definitions.Def_RealPinwheel_FiveSixths_CycleCheck
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.cycleCheck_sound {n : ℕ} (w : Array (Fin n)) (num den : Fin n → ℕ)
    (strict : Fin n → Bool) (hcheck : cycleCheck w num den strict = true)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, if strict i then (den i : ℝ) / num i < a i
      else (den i : ℝ) / num i ≤ a i) :
    ∃ (L : ℕ) (S : ℕ → Fin n), L = w.size ∧ Periodic S L ∧ Valid a S := by sorry
