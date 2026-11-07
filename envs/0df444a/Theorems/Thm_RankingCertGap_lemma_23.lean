-- Prove2me | Theorems.Thm_RankingCertGap_lemma_23
-- name    : RankingCertGap.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:40.079242+00:00
-- url     : https://prove2.me/theorems/f404ec71-1924-4c35-b270-0f6996ec4200
-- title:
--   Lemma 23, p.36 — cycle decomposition and endpoint survival
-- statement:
--   Consider a cycle with $n\ge3$ offline and online nodes and any arrival order. The following hold.
--
--   1. Every nonpeak online node is matched.
--   2. For any fixed distinct offline ranks, postponing all peak arrivals to the end leaves the complete matching unchanged.
--   3. Removing the peaks partitions the cycle into vertex-disjoint alternating path blocks. Each block has a unique minimum-time online node, with arrival times increasing along both arms away from that node.
--   4. For an endpoint reached after $r-2$ arm extensions from the minimum arrival (chain length $r\ge2$), immediately before the postponed peaks,
--   $$
--   \Pr[\mathcal E_i\mid Y_i=y]=\frac{y^{r-1}}{(r-1)!},\qquad\Pr[\mathcal E_i]=\frac1{r!}.
--   $$
--   5. The two endpoint events of the same block are mutually exclusive, and endpoint events from distinct blocks are independent.
--   6. A block whose endpoint chain lengths are $r,s$ has $r+s-2$ offline nodes.
--
--   This decomposition lets the expected loss of a cycle be charged to the sizes of its blocks.
--
--   Differences from the source:
--   - reading: "endpoint events from distinct blocks are independent" → joint independence: for any set of blocks and any choice of one endpoint per block, the probability of the intersection is the product of the probabilities; reason: the stronger reading of an ambiguous sentence; App. J.1 proves it, since the events depend on disjoint rank sets. It specializes to pairwise independence
--   - encoding: a cycle with cyclic labels $1,\dots,n$ and arrival positions $t_r$ → $t$ is a permutation of $\mathrm{Fin}\,n$, positions are $0$-based, and $j_r$ is the online vertex $t(r)$; reason: relabelling; every simple $n$-cycle in arrival order has this form
--   - encoding: the block with minimum arrival $j_q$ and chain lengths $r,s$ → indices $q,a,b$ with $r=a+2$, $s=b+2$; reason: the chain length is defined by the number of arm extensions, here $a$ or $b$
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
--   - reading: "postponing all peak arrivals to the end", "preserving the order of the remaining arrivals" (App. J.1), with the order of the peaks among themselves unspecified → the matching identity and (109), mutual exclusion and independence hold for every postponement $t'$ (nonpeak order kept, every nonpeak before every peak, any order of the peaks), and a postponement exists; reason: the stronger reading of an unspecified order; distinct peaks share no offline neighbour, so their order does not matter
--   - generalization: "every nonpeak online node is matched" for rank realizations in $[0,1]^I$ → for every rank vector $Y\in\mathbb R^I$, ties included; reason: the App. J.1 argument (the shared offline node is fresh) uses no property of the ranks; it specializes to the source's realizations
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 23, p.36; §10.1, p.35; App. J.1, p.77

import Mathlib
import Definitions.Def_RankingCertGap_RankingRun
import Definitions.Def_RankingCertGap_Score
import Definitions.Def_RankingCertGap_CycleInst

open MeasureTheory

namespace RankingCertGap

/-- **Lemma 23 (Cycle decomposition and endpoint survival).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 23, p.36, for a cycle with `n ≥ 3` (p.35). Every nonpeak online node is matched. For
fixed distinct ranks, postponing all peak arrivals to the end leaves the complete matching unchanged.
Removing the peaks partitions the cycle into vertex-disjoint alternating path blocks; each block has
a unique minimum-time online node, with arrival times increasing along both arms away from it. An
endpoint of chain length `r` satisfies, immediately before the postponed peaks,
`Pr[E_i | Y_i = y] = y^{r−1}/(r−1)!` and `Pr[E_i] = 1/r!` (eq. (109)). The two endpoint events of the
same block are mutually exclusive; endpoint events from distinct blocks are independent. A block with
endpoint chain lengths `r, s` has `r + s − 2` offline nodes.

**Formalization Note.** Blocks are indexed by their minimum arrival `q` (`IsValley`), with `a q`, `b q`
the numbers of left and right arm extensions; the endpoint chain lengths are `a q + 2` and `b q + 2`,
so `r − 1 = a q + 1`. The online vertex `j_r` is `t r` in `cycleInst t` and `t' r` in
`cycleInst t'`. The page does not fix the order of the postponed peaks, so the postponement clauses
hold for every postponement `t'` (any order of the peaks at the end), and one exists. The first
sentence holds for every rank vector, ties included. "Independent across blocks" takes the stronger
reading, joint independence: any selection of one endpoint per block in a set of blocks. -/
theorem lemma_23 {n : ℕ} (hn : 3 ≤ n) (t : Equiv.Perm (Fin n)) :
    (∀ r, ¬ IsPeak t r → ∀ Y : Fin n → ℝ, ((cycleInst t).run Y n (t r)).isSome = true) ∧
    (∃ t' : Equiv.Perm (Fin n), IsPostponement t t') ∧
    (∀ t' : Equiv.Perm (Fin n), IsPostponement t t' →
      ∀ Y : Fin n → ℝ, DistinctRanks Y → ∀ r,
        (cycleInst t).run Y n (t r) = (cycleInst t').run Y n (t' r)) ∧
    ∃ a b : Fin n → ℕ,
      (∀ q, IsValley t q → IsBlock t q (a q) (b q)) ∧
      (∀ r, IsPeak t r → ∀ q, IsValley t q → r ∉ blockOnline q (a q) (b q)) ∧
      (∀ r, ¬ IsPeak t r → ∃! q, IsValley t q ∧ r ∈ blockOnline q (a q) (b q)) ∧
      (∀ i, ∃! q, IsValley t q ∧ i ∈ blockOffline q (a q) (b q)) ∧
      (∀ q, IsValley t q → ∀ r ∈ blockOnline q (a q) (b q), r ≠ q → t q < t r) ∧
      (∀ q, IsValley t q → (blockOffline q (a q) (b q)).card = (a q + 2) + (b q + 2) - 2) ∧
      ∀ t' : Equiv.Perm (Fin n), IsPostponement t t' →
        (∀ q, IsValley t q →
          (∀ y ∈ Set.Icc (0 : ℝ) 1,
            (cycleInst t').condSafe (nonpeakCount t) (leftEndpoint q (a q)) y =
              y ^ (a q + 1) / ((a q + 1).factorial : ℝ)) ∧
          (rankMeasure n).real
              ((cycleInst t').safeEvent (nonpeakCount t) (leftEndpoint q (a q))) =
            1 / ((a q + 2).factorial : ℝ) ∧
          (∀ y ∈ Set.Icc (0 : ℝ) 1,
            (cycleInst t').condSafe (nonpeakCount t) (rightEndpoint q (b q)) y =
              y ^ (b q + 1) / ((b q + 1).factorial : ℝ)) ∧
          (rankMeasure n).real
              ((cycleInst t').safeEvent (nonpeakCount t) (rightEndpoint q (b q))) =
            1 / ((b q + 2).factorial : ℝ) ∧
          (rankMeasure n).real
              ((cycleInst t').safeEvent (nonpeakCount t) (leftEndpoint q (a q)) ∩
                (cycleInst t').safeEvent (nonpeakCount t) (rightEndpoint q (b q))) = 0) ∧
        ∀ (Q : Finset (Fin n)), (∀ q ∈ Q, IsValley t q) → ∀ s : Fin n → Bool,
          (rankMeasure n).real
              (⋂ q ∈ Q, (cycleInst t').safeEvent (nonpeakCount t)
                (if s q then rightEndpoint q (b q) else leftEndpoint q (a q))) =
            ∏ q ∈ Q, (rankMeasure n).real
              ((cycleInst t').safeEvent (nonpeakCount t)
                (if s q then rightEndpoint q (b q) else leftEndpoint q (a q))) := by sorry

end RankingCertGap
