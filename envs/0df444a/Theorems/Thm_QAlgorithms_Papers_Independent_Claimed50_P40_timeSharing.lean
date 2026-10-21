-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_timeSharing
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.timeSharing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:47:11.154657+00:00
-- url     : https://prove2.me/theorems/03e8813d-4d6c-4f73-9d2b-033bd0c59a4e
-- title:
--   Finite-code time-sharing and convexity of the capacity region
-- statement:
--   Consider a finite-dimensional memoryless channel with $s\ge1$ independent classical senders and $r\ge1$ receivers. Receiver accesses are pairwise elementwise commuting unital *-subalgebras; every receiver decodes the whole message tuple. Suppose two fixed codes have positive block lengths $m,n$, rate tuples $R,R'$, and average tuple error at most $\bar\epsilon$ at each receiver.
--
--   Pair each sender's two message sets, concatenate its encoded words, and tensor each receiver's two decoding POVMs. There exists an actual code of this specified form satisfying
--   $$
--   \bar e_j\le2\bar\epsilon\quad(j\in[r]),\qquad
--   R_i^{\rm new}=\frac{m}{m+n}R_i+\frac{n}{m+n}R_i'\quad(i\in[s]).
--   $$
--   The operational capacity region, defined by arbitrary positive error and rate slack at all sufficiently large lengths, is convex:
--   $$
--   R,R'\in\mathcal C,\quad 0\le t\le1\ \Longrightarrow\ tR+(1-t)R'\in\mathcal C.
--   $$
--   The same message pairing is used by all receivers. The finite-code assertion imposes no upper bound on $\bar\epsilon$. It describes time-sharing at the code level as well as its capacity consequence.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 2, §II, time-sharing

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Time-sharing, PDF p.2: convex operational capacity and the explicit finite-code
concatenation with doubled error tolerance and weighted rates. No upper bound on epsilon. -/
theorem timeSharing {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    Convex ℝ (capacityRegion N) ∧
    ∀ {m n : ℕ} (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (epsilon : ℝ),
      (∀ j, averageTupleError c j ≤ epsilon) → (∀ j, averageTupleError d j ≤ epsilon) →
      ∃ e : MultiwayBlockCode N (m + n), IsConcatenation c d e ∧
        (∀ j, averageTupleError e j ≤ 2 * epsilon) ∧
        ∀ i, codeRate e i =
          (m : ℝ) / (m + n) * codeRate c i + (n : ℝ) / (m + n) * codeRate d i := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
