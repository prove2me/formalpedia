-- Prove2me | Theorems.Thm_ProportionalTSP_Exact_proposition_4_1
-- name    : ProportionalTSP.Exact.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:00:32.703217+00:00
-- url     : https://prove2.me/theorems/f31706cb-4a37-4549-8e0b-12d417991508
-- title:
--   Proposition 4.1 — Restricted DP solves TSP with its stated runtime
-- statement:
--   Assume the standing complete-cross graph model, generic $w$, $1\le k\le m$, and $n=m+k\ge3$. For every start $s\in R$, the explicitly defined recurrence (4.1), with its exceptional start state, returns a minimum-cost tour or correctly reports nonexistence:
--   $$\mathrm{restrictedDP}(G,w,\mathcal C(w),s)\text{ is a correct TSP answer}.$$
--   One finite deterministic program computes this same recurrence's answer in $O^*(N_{m,k})$ time, uniformly over all such inputs. The returned edge set comes from a recovered predecessor path and the original closing edge.
--
--   Differences from the source:
--   - encoding: finite labeled vertices and assignments on L and R → Fin-indexed vertices, with paper index equal to Lean index plus one; reason: relabeling preserves every finite instance; section hypotheses remain explicit
--   - encoding: Hamiltonian cycles counted as undirected cycles → finite unordered edge sets represented by a spanning simple cyclic list of length at least three; reason: rotations and reversal identify the same cycle, including in the parity count
--   - encoding: unreachable DP entries have value positive infinity → Option-valued path entries and an empty final list giving none; reason: unreachable entries never acquire a default finite objective value; predecessor paths recover the tour
--   - encoding: deterministic polynomial or O* running time → a finite RAM program, uniform positive coefficient and natural exponent, and its evaluated instruction count; reason: the explicit language charges combinatorial instructions and allows input reals only to be copied, added, and compared; signed values are pairs of sums
--   - encoding: states processed by increasing size, ties among equal-cost paths unspecified, answer a tour → equal-size sets ordered by subset code, extensions in word order, ties keep the earlier path, and the program outputs the edge-indicator matrix of the resulting tour; reason: these fix the choices the source leaves free without changing the recurrence or the optimal value, and each choice is implementable at polynomial overhead
-- source:
--   Ethan X. Fang, Shengtao Guo, Junwei Lu, Yuan Yao, STOC 2027 submission #481 (October 2026), Proposition 4.1, PDF p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/481.pdf

import Definitions.Def_ProportionalTSP_Exact_Symbolic

noncomputable section

namespace ProportionalTSP.Exact
open scoped Classical

theorem proposition_4_1 :
    (∀ (m k : ℕ) [NeZero m] [NeZero k], k ≤ m → 3 ≤ m+k →
      ∀ (G : SimpleGraph (Vertex m k)), SectionGraph G →
      ∀ (w : Sym2 (Vertex m k) → ℝ), Generic (cross w) → ∀ s : Fin k,
        CorrectAnswer G w (restrictedDP G w (vertexList m k)
          (compatibleFamily (cross w)) (.inr s))) ∧
    EfficientRestrictedDP := by sorry

end ProportionalTSP.Exact
