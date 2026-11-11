-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_7_2
-- name    : RWCuckoo.Threshold.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:33:18.81274+00:00
-- url     : https://prove2.me/theorems/5daa2cf3-7fe2-4d05-9061-2dbfdcfdc39d
-- title:
--   Lemma 7.2 — sprinkling: Ω(β^d ε_Δ n) vertex-disjoint paths of length t to the empty cells
-- statement:
--   There are absolute constants $c>0$ and $C$ such that the following holds. Let $d\ge3$, $\varepsilon^*_d<\varepsilon\le1$, and fix an integer $t\ge1$ and $\beta\in(0,1]$ (which may depend on $d$). For all large $n$, with probability at least $1-C/n$ over the hashes, every matching with $|U_t|\ge\beta n$ has at least
--   $$c\,\beta^d\,\varepsilon_\Delta\,n$$
--   vertex-disjoint paths of length $t$ to the set $E$ of empty cells.
--
--   Sprinkling jump-starts the backward expansion from the empty cells in the regime closest to the threshold.
--
--   Differences from the source:
--   - encoding: m = ⌊(1 − ε)n⌋ keys (ε > ε∗_d) → hypothesis ε ≤ 1; reason: for ε > 1 the floor clamps the key count to 0, which is not the paper's setting; m = ⌊(1 − ε)n⌋ is a key count only for ε ≤ 1
--   - encoding: O(·), Ω(·), probability 1 − O(1/n) / 'w.h.p.' with absolute constants (footnote 2, p. 4; p. 5), 'for large n' → explicit constants ∃ C (and ∃ c > 0 for Ω) quantified before d and ε; ∃ n0 depending on d, ε (and the other fixed parameters) with ∀ n ≥ n0; probability bounds as μ(bad) ≤ ofReal(C/n); reason: the paper's definition of its asymptotic notation; one C serves several O's because every bound is monotone in C
--   - encoding: matching M : [m] → [n] injective with M(x) ∈ {h_1(x), …, h_d(x)} → Matching h records a matching index idx x with M(x) = h x (idx x); reason: every matching has such an index choice; the walks depend only on the cells, and an admissible configuration needs the matching index (Definition 5.2)
--   - reading: vertex-disjoint paths of length t to E → a family of r paths (sequences of t + 1 cells, per the paper's definition of a path) whose cell sets are pairwise disjoint; reason: the paper defines a path as a sequence of cells (p. 22); vertex-disjoint means no two share a cell
--   - encoding: on a hash-only event of probability 1 − O(1/n) (w.h.p.), the claim holds for every matching (configuration, set) → the uniform measure of the set of hash assignments of the first m keys on which the universal claim fails is at most C/n; reason: the claim involves only the first m keys; an event of all hashes on which it holds projects to a set of first-m hash assignments of at least the same probability, and the success set is itself a hash-only event (finite space)
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 30 (PDF 31), Lemma 7.2

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk
import Definitions.Def_RWCuckoo_Threshold_Expansion

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma 7.2, sprinkling (p. 30): there are absolute `c, C > 0` such that for `d ≥ 3`,
`ε∗_d < ε ≤ 1`, fixed `t ≥ 1` and `β ∈ (0, 1]`, w.h.p. every matching with `|U_t| ≥ βn` has at
least `c β^d ε_Δ n` vertex-disjoint paths of length `t` to the empty cells `E`. -/
theorem lemma_7_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, epsStar d < ε → ε ≤ 1 →
      ∀ t : ℕ, 1 ≤ t → ∀ β : ℝ, 0 < β → β ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        hashMeasure (numKeys n ε) d n
            {h | ¬ ∀ M : Matching h, β * n ≤ (M.farCells t).card →
              ∃ (r : ℕ) (P : Fin r → Fin (t + 1) → Fin n),
                c * β ^ d * epsDelta d ε * n ≤ r ∧ (∀ a, M.IsPathTo (P a) M.empty) ∧
                ∀ a b, a ≠ b → Disjoint (Set.range (P a)) (Set.range (P b))} ≤
          ENNReal.ofReal (C / n) := by sorry

end RWCuckoo.Threshold
