-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_corollary1_series_bound_keeps_LRB
-- name    : RoslingAssembly.SeriesEquiv.corollary1_series_bound_keeps_LRB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:41.385372+00:00
-- url     : https://prove2.me/theorems/c84bf2a2-0367-4be0-b54a-03c016e4d448
-- title:
--   Corollary 1 — adjacent series bound
-- statement:
--   The realization and persistence conclusions of Theorem 1 continue to hold when the upper production limit in Lemma 1 is replaced by the adjacent position $X^L_{i+1,t}$. Thus, with the bound $Y_{it}\le\max(X_{it},X^L_{i+1,t})$ for $i<N$ and Lemma 2’s lower bound, the same long-run-balance conclusion follows.
--
--   $$\sum_{r=1}^{s}\xi_r>\max_iX_{i1}\quad\Longrightarrow\quad\forall t\ge s+M_N+1,\ \text{long-run balance at }t.$$
--
--   This connects series-system feasibility to the balance condition needed by the equivalent-system theorem.
--
--   **Formalization Note** Demand paths are nonnegative and feasibility is pathwise in this statement.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 569, Corollary 1

import Definitions.Def_RoslingAssembly_SeriesEquiv_Dynamics

namespace RoslingAssembly.SeriesEquiv

/-- Rosling, Corollary 1, p. 569: Theorem 1 with the adjacent series bound. -/
theorem corollary1_series_bound_keeps_LRB (S : Model) (x0 : InitialPositions)
    (π : Policy) (ω : ℕ → ℝ) (hTree : S.ValidTree)
    (hInitial : S.WellFormedInitial x0)
    (hDemandNonneg : ∀ k, 0 ≤ ω k)
    (hFeasible : S.PathFeasible x0 π ω)
    (hSeriesBound : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
      S.SeriesNoExcessAt x0 π ω i t)
    (hLemma2 : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
      S.MinProductionAt x0 π ω i t) :
    (∀ t ≥ 1, S.LongRunBalance x0 π ω t →
      S.LongRunBalance x0 π ω (t + 1)) ∧
    (∀ s : ℕ, (∑ r ∈ Finset.range s, ω r) >
      (Finset.Icc 1 S.N).sup' (by
        have hn : 1 ∈ Finset.Icc 1 S.N := Finset.mem_Icc.mpr ⟨le_refl 1, hTree.1⟩
        exact Finset.nonempty_iff_ne_empty.mpr (Finset.ne_empty_of_mem hn))
        (fun i => x0 i 1) →
      ∀ t ≥ s + S.M S.N + 1, S.LongRunBalance x0 π ω t) := by sorry

end RoslingAssembly.SeriesEquiv
