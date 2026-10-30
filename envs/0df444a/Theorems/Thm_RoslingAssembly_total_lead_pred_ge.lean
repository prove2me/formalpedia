-- Prove2me | Theorems.Thm_RoslingAssembly_total_lead_pred_ge
-- name    : RoslingAssembly.total_lead_pred_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:44:30.752388+00:00
-- url     : https://prove2.me/theorems/6a0b876d-e30d-4885-b656-fcf0b5314636
-- title:
--   Predecessors have larger total lead time: $M_i+l_k\le M_k$ for $k\in B(i)$
-- statement:
--   In every assembly network with lead times $l$, for every item $i$ and every predecessor $k\in B(i)$,
--   $$M_i+l_k\le M_k ;$$
--   in particular $M_i\le M_k$, so $M_k-M_i$ is the nonnegative number of periods between the extra order of $k$ and that of $i$ in the proof of Theorem 4(i).
--
--   **Formalization Note** Items are `Fin N`, 0-based. The form $M_i+l_k\le M_k$ contains $M_i\le M_k$.
--
--   Differences from the source:
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578 (unnumbered; implicit in 'the first M_k − M_i periods')

import Mathlib
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_M

namespace RoslingAssembly

/-- **Predecessors have larger total lead time** (Appendix B, Proof of Theorem 4, p. 578,
unnumbered). Rosling, *Optimal Inventory Policies for Assembly Systems under Random Demands*,
Operations Research 37(4), 1989, p. 578: "The additional cost of this policy is for the first
M_m − M_i periods (capitalized to period M_m − M_i + 1) Σ_{k∈B(i)} h_k · α^{l_k}(1 + α + . . . +
α^{M_k−M_i−1}) · α^{−(M_k−M_i)}", which treats `M_k − M_i` as a period count for `k ∈ B(i)`.

For every predecessor `k ∈ B(i)` of an item `i`, `M_i + l_k ≤ M_k`; in particular `M_i ≤ M_k`.

**Formalization Note.** Items are `Fin N`, 0-based. The stated form `M_i + l_k ≤ M_k` is the
stronger one (it contains `M_i ≤ M_k`). -/
theorem total_lead_pred_ge {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) :
    ∀ k ∈ net.B i, net.M ℓ i + ℓ k ≤ net.M ℓ k := by sorry

end RoslingAssembly
