-- Prove2me | Theorems.Thm_SparseDisc_kostochka_thomason_degeneracy
-- name    : SparseDisc.kostochka_thomason_degeneracy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:52:11.581046+00:00
-- url     : https://prove2.me/theorems/28da03b9-022c-41ca-9ee5-c527a60c9702
-- title:
--   Kostochka–Thomason: $K_r$-minor-free graphs are $O(r\sqrt{\log r})$-degenerate
-- statement:
--   There is an absolute constant $C > 0$ such that for every $r \ge 1$, every finite graph with no $K_r$ minor is $\lfloor C r \sqrt{\log r} \rfloor$-degenerate. In the words of the proof of Theorem 1.9, "$K_r$-minor-free graphs are $O(r\sqrt{\log r})$-degenerate" [Kostochka 1984, Thomason 1984].
--
--   This external fact turns the degeneracy bound of Theorem 1.9 into part (a)'s bound for $K_r$-minor-free patterns.
--
--   **Formalization Note** The constant $C$ is chosen before $r$ and the graph; $\log$ is the natural logarithm (another base only changes $C$). Minors are the published branch-set model `RobertsonSeymour1986.GM5.IsMinor` and $K_r$ is the complete graph on `Fin r`.
--
--   Differences from the source:
--   - encoding: O(r√log r)-degenerate → ∃ C > 0, ∀ r ≥ 1: every K_r-minor-free finite graph has an ordering with at most ⌊C r √(log r)⌋ later neighbours per vertex; reason: an integer degeneracy is at most x iff it is at most ⌊x⌋; for r = 1 the graph is empty, so a constant uniform over all r ≥ 1 is the same as an asymptotic constant
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), proof of Theorem 1.9, p.46 (citing [Kos84, Tho84])

import Mathlib
import Definitions.Def_SparseDisc_HasDegenOrdering
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace SparseDisc

/-- **Kostochka–Thomason degeneracy bound**, as cited in the proof of Theorem 1.9
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), proof of Theorem 1.9, p.46: "Kr-minor-free graphs are
O(r√log r)-degenerate [Kos84, Tho84]"). There is an absolute constant `C > 0` such that for every
`r ≥ 1`, every finite graph with no `K_r` minor is `⌊C r √(log r)⌋`-degenerate.

**Formalization Note** `O(r√log r)` is an absolute constant `C`, chosen before `r` and the graph;
`log` is the natural logarithm (the base only changes `C`). Minors are the published branch-set
model `RobertsonSeymour1986.GM5.IsMinor`; `K_r` is `⊤` on `Fin r`. -/
theorem kostochka_thomason_degeneracy :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → ∀ (V : Type) [Fintype V] (H : SimpleGraph V),
      ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin r)) H →
      HasDegenOrdering H ⌊C * r * Real.sqrt (Real.log r)⌋₊ := by sorry

end SparseDisc
