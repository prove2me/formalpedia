-- Prove2me | Theorems.Thm_RoslingAssembly_geometric_identity
-- name    : RoslingAssembly.geometric_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:48:52.198352+00:00
-- url     : https://prove2.me/theorems/c8c78c18-4e21-4bd4-a055-5871d2470f04
-- title:
--   Cost of the extra predecessor units before item $i$ is built
-- statement:
--   For every discount factor $0<\alpha<1$, every item $i$ and arbitrary real installation costs,
--   $$\sum_{k\in B(i)}h_k\alpha^{l_k}\big(1+\alpha+\dots+\alpha^{M_k-M_i-1}\big)\alpha^{-(M_k-M_i)}
--   =\sum_{k\in B(i)}h_k\alpha^{l_k}\,\frac{\alpha^{-(M_k-M_i)}-1}{1-\alpha}.$$
--
--   The left side is the paper's cost of holding the extra units of the predecessors during the first $M_m-M_i$ periods, capitalized to period $M_m-M_i+1$.
--
--   **Formalization Note** The geometric sum has $M_k-M_i$ terms, a nonnegative number since $M_i\le M_k$ for $k\in B(i)$.
--
--   Differences from the source:
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: α^{−M} → integer power `α ^ (-(M : ℤ))` (zpow); reason: Lean convention; same values for α > 0
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578, first and second display

import Mathlib
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_M
import Definitions.Def_RoslingAssembly_Network_h

namespace RoslingAssembly

/-- **Cost of the extra predecessor units before item i is built** (Appendix B, Proof of
Theorem 4, p. 578, first and second display). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 578: "The additional cost of
this policy is for the first M_m − M_i periods (capitalized to period M_m − M_i + 1)
Σ_{k∈B(i)} h_k · α^{l_k}(1 + α + . . . + α^{M_k−M_i−1}) · α^{−(M_k−M_i)} or equivalently
Σ_{k∈B(i)} h_k · α^{l_k}(α^{−(M_k−M_i)} − 1)/(1 − α)."

For `0 < α < 1`, every item `i` and arbitrary real installation costs `H`,
$$\sum_{k\in B(i)}h_k\alpha^{l_k}\Big(\sum_{j=0}^{M_k-M_i-1}\alpha^j\Big)\alpha^{-(M_k-M_i)}
=\sum_{k\in B(i)}h_k\alpha^{l_k}\,\frac{\alpha^{-(M_k-M_i)}-1}{1-\alpha}.$$

**Formalization Note.** The finite geometric sum is `Finset.range (M_k − M_i)` with natural
subtraction, which is exact because `M_i ≤ M_k` for `k ∈ B(i)`; the negative powers are integer
powers (`zpow`). -/
theorem geometric_identity {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (α : ℝ)
    (hα : 0 < α ∧ α < 1) (i : Fin N) :
    ∑ k ∈ net.B i, net.h H k * α ^ ℓ k * (∑ j ∈ Finset.range (net.M ℓ k - net.M ℓ i), α ^ j) *
        α ^ (-((net.M ℓ k : ℤ) - net.M ℓ i)) =
      ∑ k ∈ net.B i, net.h H k * α ^ ℓ k * (α ^ (-((net.M ℓ k : ℤ) - net.M ℓ i)) - 1) / (1 - α) := by sorry

end RoslingAssembly
