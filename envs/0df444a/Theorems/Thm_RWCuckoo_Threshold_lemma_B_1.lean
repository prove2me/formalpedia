-- Prove2me | Theorems.Thm_RWCuckoo_Threshold_lemma_B_1
-- name    : RWCuckoo.Threshold.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:32:10.79317+00:00
-- url     : https://prove2.me/theorems/dc5771e8-d27f-4fca-acdd-80e05b7d97cf
-- title:
--   Lemma B.1 — backtracking costs at most a factor d/(d − 2) ≤ 3 over the nonbacktracking insertion
-- statement:
--   Fix the hashes $h$ of the first $m$ keys and $g$ of the new key, and a table in which the first $m$ keys are placed by a matching $M$, each at its matching index (the prepared table is such a table). Consider inserting the new key by the ordinary random-walk insertion and by the nonbacktracking insertion, in which an evicted key never chooses the index at which it was just evicted. For $d\ge3$,
--   $$\mathbb E[\#\text{probes of the ordinary insertion}]\;\le\;\frac{d}{d-2}\;\mathbb E[\#\text{probes of the nonbacktracking insertion}],\qquad \frac{d}{d-2}\le3,$$
--   the expectations being over the probe choices only, in $[0,\infty]$.
--
--   This is the first of the three steps comparing an insertion with the frozen-matching walk (App. B, p. 41); it lets the analysis forbid backtracking at the cost of a constant factor.
--
--   Differences from the source:
--   - generalization: the prepared table (the matching produced by the first m insertions) → every matching M of the first m keys, each key at its matching index; reason: every prepared table is a matching of the first m keys with the indices the keys used; the statement for all matchings specializes to it
--   - reading: d not specified in the lemma → 3 ≤ d; reason: the factor d/(d − 2) is meaningful only for d ≥ 3, the range of Appendix B (Theorem 4.1: 'Fix d ≥ 3')
--   - encoding: expected number of probes, fixed hashes and table → lintegral in ℝ≥0∞ of the ℕ∞-valued number of placements over the probe stream (Fin d for the new key, Fin (d − 1) for evicted keys in the nonbacktracking insertion); reason: expectations of possibly infinite costs; uniform choice among the d − 1 other indices encoded as (j + 1 + u) mod d
-- source:
--   Hu, Kuszmaul, Liang, Random-Walk Cuckoo Hashing is Efficient up to the Critical Load Threshold, STOC 2027 submission (manuscript sha256 1fcebf33…), p. 41 (PDF 42), Lemma B.1

import Mathlib
import Definitions.Def_RWCuckoo_Threshold_LoadThreshold
import Definitions.Def_RWCuckoo_Threshold_Insertion
import Definitions.Def_RWCuckoo_Threshold_FrozenWalk

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RWCuckoo.Threshold

/-- Lemma B.1 (p. 41): fix the hashes of all `m + 1` keys and the prepared table (here: any
matching `M` of the first `m` keys, each at its matching index). The expected number of probes
of the ordinary insertion of the new key is at most `d/(d − 2)` times that of the nonbacktracking
insertion, and `d/(d − 2) ≤ 3`. -/
theorem lemma_B_1 (d : ℕ) (hd : 3 ≤ d) (m n : ℕ) (h : Hashes m d n) (g : Fin d → Fin n)
    (M : Matching h) :
    expInsertionCost (withNewKey h g) M.table (Fin.last m) ≤
        ENNReal.ofReal ((d : ℝ) / ((d : ℝ) - 2)) *
          expNBCost (withNewKey h g) M.table (Fin.last m) ∧
      (d : ℝ) / ((d : ℝ) - 2) ≤ 3 := by sorry

end RWCuckoo.Threshold
