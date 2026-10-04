-- Prove2me | Theorems.Thm_TaoFivePrimes_three_primes_of_representationCount_pos
-- name    : TaoFivePrimes.three_primes_of_representationCount_pos
-- status  : Proved
-- author  : @Patrick
-- created : 2026-09-07T02:18:42.823716+00:00
-- url     : https://prove2.me/theorems/65f29d83-beef-43e1-ab65-bbbc5000e7d5
-- title:
--   A positive weighted count yields three odd primes (Tao, after equation 8.10)
-- statement:
--   Let $x,H$ be natural numbers with $x\geq4000$, and let $R(x,H)$ be Tao's weighted representation count from equation (8.10), with $K=1000$. If $R(x,H)>0$, then there are three odd primes $p_1,p_2,p_3$ whose sum $m$ satisfies
--
--   $$x\leq m+H,\qquad m+2\leq x,\qquad m=p_1+p_2+p_3.$$
--
--   The primes may repeat. With $H=4\cdot10^{14}$, this is the witness-extraction step that turns the analytic positivity estimate into Theorem 8.2 of the five-primes paper.
--
--   **Formalization Note** The interval is written with addition to avoid truncated natural subtraction. The lower bound $x\geq4000$ ensures that both square-root sieves include the prime 2, including the sieve at the smaller scale $x/1000$.
-- source:
--   Terence Tao, https://arxiv.org/abs/1201.6656, Section 8, implication immediately following equation (8.10), with K=10^3 as chosen after (8.11). Generalized to a gap budget H.

import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

theorem TaoFivePrimes.three_primes_of_representationCount_pos (x H : ℕ)
    (hx : 4000 ≤ x) (hcount : 0 < representationCount x H) :
    ∃ m : ℕ, x ≤ m + H ∧ m + 2 ≤ x ∧
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
        Odd p₁ ∧ Odd p₂ ∧ Odd p₃ ∧ p₁ + p₂ + p₃ = m := by sorry
