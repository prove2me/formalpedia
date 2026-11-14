-- Prove2me | Theorems.Thm_RvsCert_lemma_4
-- name    : RvsCert.lemma_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:48:45.144858+00:00
-- url     : https://prove2.me/theorems/dd6f3207-5e6d-4731-a9b8-a23f955df8bf
-- title:
--   Lemma 4 — $C_0(f)=\Omega(n^2)$
-- statement:
--   Let $f_n$ be the champion function. There is a constant $c>0$ such that for every $n>0$,
--   $$
--   C_0(f_n)\ \ge\ c\,n^2.
--   $$
--   Since $C(f_n)\ge C_0(f_n)$, this gives the certificate lower bound of Theorem 1.
--
--   Differences from the source:
--   - encoding: the function f on (X, Y) with numbers in log n bits → the bit layout `Idx n` with fixed widths wX n = ⌈log₂(2n²+1)⌉, wY n = ⌊log₂ n⌋+1, ⊥ = 0, athlete (c,b) = 1+cn+b, 0-based positions, card entry j for the j-th opponent in increasing order; reason: the paper fixes only O(log n)-bit numbers; this is one such injective encoding
--   - reading: C0(f) = Ω(n²) → ∃ c > 0, ∀ n > 0, c·n² ≤ C0(f_n); reason: asymptotic notation over the family, constant chosen before n
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 4, p.3

import Mathlib
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_C0

namespace RvsCert

/-- **Lemma 4** (p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "There are no short 0-certificates:
C0(f) = Ω(n²)." There is a constant `c > 0` with `c·n² ≤ C0(champion n)` for every `n > 0`. -/
theorem lemma_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n → c * (n : ℝ) ^ 2 ≤ (C0 (champion n) : ℝ) := by sorry

end RvsCert
