-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_6_4
-- name    : RWCuckoo.Threshold.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:08.745068+00:00
-- url     : https://prove2.me/theorems/e33ba248-ed75-4ab6-bf84-e8bf5aabe847
-- title:
--   Lemma 6.4 — structured sets expand by Ω(d), and by d − O(√(d log d)) when the roots are few
-- statement:
--   There are absolute constants $D_0$, $c>0$, $C'$ and $C$ such that for $d\ge D_0$ and $\varepsilon^*_d<\varepsilon<e^{-d/4}$, for all large $n$, with probability at least $1-C/n$: for every matching and every structured set $S$ with root set $R$, the numbers $r=|R|$ and $k=|S\setminus R|$ satisfy the following whenever $k\ge\log^2 n$.
--
--   (a) If $k\le n/d$ and $r\log(en/r)\le dk/4$, then $|N(S)|\ge c\,d\,k$.
--
--   (b) If $k\le n/d^2$ and $r\log(en/r)\le k\log d$, then
--   $$|N(S)|\ge\bigl(d-C'\sqrt{d\log d}\bigr)k .$$
--
--   Part (b) is the near-perfect expansion of sets grown from a small root set, proved by a union bound over witness forests.
--
--   Differences from the source:
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - encoding: standing assumption d ≥ D0 for a sufficiently large absolute D0 (pp. 13, 16) → ∃ D0 : ℕ, ∀ d ≥ D0; reason: the paper's 'sufficiently large absolute constant'; D0 ≥ 10^6 is implied by taking D0 larger
--   - encoding: log² n and r log(en/r) → (Real.log n)^2 and R.card * Real.log (exp 1 * n / R.card); reason: log² n means (log n)²; at r = 0 the Lean term is 0, the limit of r log(en/r)
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 24 (PDF 25), Lemma 6.4

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 6.4, expansion of structured sets (p. 24): for `d ≥ D0` and `ε∗_d < ε < e^{−d/4}`, w.h.p.,
for every matching and every structured set `S` with root set `R`, with `r = |R|`,
`k = |S \ R| ≥ log² n`: (a) if `k ≤ n/d` and `r log(en/r) ≤ dk/4` then `|N(S)| ≥ c d k`; (b) if
`k ≤ n/d²` and `r log(en/r) ≤ k log d` then `|N(S)| ≥ (d − C' √(d log d)) k`; `c`, `C'` absolute. -/
theorem lemma_6_4 :
    ∃ D0 : ℕ, ∃ c C' C : ℝ, 0 < c ∧ 0 < C' ∧ 0 < C ∧ ∀ d : ℕ, D0 ≤ d → ∀ ε : ℝ,
      epsStar d < ε → ε < Real.exp (-(d : ℝ) / 4) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ (M : Matching h) (S R : Finset (Fin n)), M.IsStructured S R →
              Real.log n ^ 2 ≤ (S \ R).card →
              (((S \ R).card : ℝ) ≤ n / d →
                  R.card * Real.log (Real.exp 1 * n / R.card) ≤ d * (S \ R).card / 4 →
                  c * d * (S \ R).card ≤ (M.nbhd S).card) ∧
              (((S \ R).card : ℝ) ≤ n / (d : ℝ) ^ 2 →
                  R.card * Real.log (Real.exp 1 * n / R.card) ≤ (S \ R).card * Real.log d →
                  (d - C' * Real.sqrt (d * Real.log d)) * (S \ R).card ≤ (M.nbhd S).card)} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
