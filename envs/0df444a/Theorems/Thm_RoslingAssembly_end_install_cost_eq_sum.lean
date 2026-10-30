-- Prove2me | Theorems.Thm_RoslingAssembly_end_install_cost_eq_sum
-- name    : RoslingAssembly.end_install_cost_eq_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:45:01.760997+00:00
-- url     : https://prove2.me/theorems/a9d33e92-bac5-4dff-8120-39d01262a3c5
-- title:
--   $H_1=\sum_{i=1}^Nh_i$
-- statement:
--   In every assembly network, for every vector of installation holding costs $H\in\mathbb R^N$, the installation holding cost of the end item equals the sum of all echelon holding costs:
--   $$H_1=\sum_{i=1}^Nh_i,\qquad h_i=H_i-\sum_{k\in P(i)}H_k .$$
--
--   It ties the backlog coefficient $p+H_1$ of (2) to the echelon costs.
--
--   **Formalization Note** The end item is Lean item $0$.
--
--   Differences from the source:
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix A, §1, p. 575 (unnumbered)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_h

namespace RoslingAssembly

/-- **H_1 = Σ h_i** (Appendix A1, p. 575, unnumbered). Rosling, *Optimal Inventory Policies for
Assembly Systems under Random Demands*, Operations Research 37(4), 1989, Appendix A, §1, p. 575:
"Recalling that H_1 = Σ_{i=1}^N h_i, the modifications are".

The installation holding cost of the end item equals the sum of the echelon holding costs of all
items, `H_1 = Σ_i h_i`, where `h_i = H_i − Σ_{k∈P(i)} H_k`.

**Formalization Note.** Items are `Fin N`, 0-based: the end item (paper item 1) is Lean item
`0`; `[NeZero N]` makes it exist. `H` is arbitrary. -/
theorem end_install_cost_eq_sum {N : ℕ} [NeZero N] (net : Network N) (H : Fin N → ℝ) :
    H 0 = ∑ i, net.h H i := by sorry

end RoslingAssembly
