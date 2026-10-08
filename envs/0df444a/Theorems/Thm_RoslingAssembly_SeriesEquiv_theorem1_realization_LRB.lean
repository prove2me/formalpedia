-- Prove2me | Theorems.Thm_RoslingAssembly_SeriesEquiv_theorem1_realization_LRB
-- name    : RoslingAssembly.SeriesEquiv.theorem1_realization_LRB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:34.314239+00:00
-- url     : https://prove2.me/theorems/6fe7d0d6-22c0-46b7-8410-0501efbb549b
-- title:
--   Theorem 1 — realization of long-run balance
-- statement:
--   Fix a nonnegative demand path and a feasible policy satisfying the production bounds of Lemmas 1 and 2. Long-run balance, once present, persists into the next period. If accumulated demand through period $s$ exceeds the largest initial pre-order position, then balance holds by period $s+M_N+1$ and thereafter.
--
--   $$\sum_{r=1}^{s}\xi_r>\max_{1\le i\le N}X_{i1}\quad\Longrightarrow\quad\forall t\ge s+M_N+1,\ \text{long-run balance at }t.$$
--
--   This is the finite-time pathwise assertion behind Theorem 2.
--
--   **Formalization Note** The result is pathwise; the almost-sure existence of a threshold $s$ from positive mean demand is separate. Past pipeline consistency is explicit.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, pp. 568–569, Theorem 1

import Definitions.Def_RoslingAssembly_SeriesEquiv_Dynamics

namespace RoslingAssembly.SeriesEquiv

/-- Rosling, Theorem 1, pp. 568–569: preservation and a deterministic
realization bound after accumulated demand overtakes initial inventory. -/
theorem theorem1_realization_LRB (S : Model) (x0 : InitialPositions)
    (π : Policy) (ω : ℕ → ℝ) (hTree : S.ValidTree)
    (hInitial : S.WellFormedInitial x0)
    (hDemandNonneg : ∀ k, 0 ≤ ω k)
    (hFeasible : S.PathFeasible x0 π ω)
    (hLemma1 : ∀ t ≥ 1, ∀ i ∈ Finset.Icc 1 S.N,
      S.NoExcessAt x0 π ω i t)
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
