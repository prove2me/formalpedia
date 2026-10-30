-- Prove2me | Theorems.Thm_RoslingAssembly_total_cost_increase
-- name    : RoslingAssembly.total_cost_increase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:49:44.955988+00:00
-- url     : https://prove2.me/theorems/a1e72c64-d147-4e2a-9901-a10d5eda4713
-- title:
--   Total cost increase per extra unit and its sign
-- statement:
--   Let $0<\alpha\le1$ and let $i$ be an item.
--   1. If $\alpha<1$, the cost of the extra predecessor units before period $M_m-M_i+1$ plus the cost of holding item $i$ and its predecessors forever from then on is the **total cost increase**:
--   $$\sum_{k\in B(i)}h_k\alpha^{l_k}\frac{\alpha^{-(M_k-M_i)}-1}{1-\alpha}+\frac{h_i\alpha^{l_i}+\sum_{k\in B(i)}h_k\alpha^{l_k}}{1-\alpha}
--   =\frac{\alpha^{l_i}\big(h_i+\sum_{k\in B(i)}h_k\alpha^{-(M_{s(k)}-M_{s(i)})}\big)}{1-\alpha}.$$
--   2. If $\alpha<1$, the total cost increase is negative if and only if $h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}}<0$, the hypothesis of Theorem 4(i).
--   3. For every $0<\alpha\le1$: $h_i+\sum_{k\in B(i)}h_k\alpha^{-(M_{s(k)}-M_{s(i)})}<0$ if and only if $h_i\alpha^{-M_{s(i)}}+\sum_{k\in B(i)}h_k\alpha^{-M_{s(k)}}<0$.
--
--   **Formalization Note** Clause 3 covers $\alpha=1$, where the formulas of clauses 1–2 would divide by zero.
--
--   Differences from the source:
--   - generalization: the sign of the total cost increase, for α < 1 → also clause 3, the equivalence of the bracket's sign with the hypothesis for every 0 < α ≤ 1; reason: an additional true clause; clauses 1–2 are the paper's displays
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
--   - encoding: α^{−M} → integer power `α ^ (-(M : ℤ))` (zpow); reason: Lean convention; same values for α > 0
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, Appendix B, Proof of Theorem 4, p. 578, third and fourth display

import Mathlib
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_M
import Definitions.Def_RoslingAssembly_Network_Ms
import Definitions.Def_RoslingAssembly_Network_h

namespace RoslingAssembly

/-- **Total cost increase per extra unit and its sign** (Appendix B, Proof of Theorem 4, p. 578,
third and fourth display). Rosling, *Optimal Inventory Policies for Assembly Systems under Random
Demands*, Operations Research 37(4), 1989, p. 578: "The cost of holding item i forever from period
M_m − M_i + 1 on is (h_i · α^{l_i} + Σ_{k∈B(i)} h_k · α^{l_k}) / (1 − α). So, the total cost
increase is α^{l_i}(h_i + Σ_{k∈B(i)} h_k · α^{−(M_{s(k)}−M_{s(i)})}) / (1 − α) < 0 by assumption."

Let `0 < α ≤ 1` and `i` be an item; `H` arbitrary real installation costs.
1. If `α < 1`, the cost of the predecessor units before period `M_m − M_i + 1` plus the cost of
   holding item `i` and its predecessors forever from then on equals the total cost increase:
   $$\sum_{k\in B(i)}h_k\alpha^{l_k}\frac{\alpha^{-(M_k-M_i)}-1}{1-\alpha}
   +\frac{h_i\alpha^{l_i}+\sum_{k\in B(i)}h_k\alpha^{l_k}}{1-\alpha}
   =\frac{\alpha^{l_i}\big(h_i+\sum_{k\in B(i)}h_k\alpha^{-(M_{s(k)}-M_{s(i)})}\big)}{1-\alpha}.$$
2. If `α < 1`, this total cost increase is negative exactly when
   `h_i α^{−M_{s(i)}} + Σ_{k∈B(i)} h_k α^{−M_{s(k)}} < 0` (the hypothesis of Theorem 4(i)).
3. For every `0 < α ≤ 1`,
   `h_i + Σ_{k∈B(i)} h_k α^{−(M_{s(k)}−M_{s(i)})} < 0` exactly when
   `h_i α^{−M_{s(i)}} + Σ_{k∈B(i)} h_k α^{−M_{s(k)}} < 0`.

**Formalization Note.** Negative powers are integer powers (`zpow`); total lead times are cast
to `ℤ` before subtracting. Clause 3 covers `α = 1`, where clauses 1–2 would divide by zero. -/
theorem total_cost_increase {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (α : ℝ)
    (hα : 0 < α ∧ α ≤ 1) (i : Fin N) :
    (α < 1 →
      ∑ k ∈ net.B i, net.h H k * α ^ ℓ k * (α ^ (-((net.M ℓ k : ℤ) - net.M ℓ i)) - 1) / (1 - α) +
          (net.h H i * α ^ ℓ i + ∑ k ∈ net.B i, net.h H k * α ^ ℓ k) / (1 - α) =
        α ^ ℓ i * (net.h H i +
          ∑ k ∈ net.B i, net.h H k * α ^ (-((net.Ms ℓ k : ℤ) - net.Ms ℓ i))) / (1 - α)) ∧
    (α < 1 →
      (α ^ ℓ i * (net.h H i +
          ∑ k ∈ net.B i, net.h H k * α ^ (-((net.Ms ℓ k : ℤ) - net.Ms ℓ i))) / (1 - α) < 0 ↔
        net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) +
          ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) < 0)) ∧
    (net.h H i + ∑ k ∈ net.B i, net.h H k * α ^ (-((net.Ms ℓ k : ℤ) - net.Ms ℓ i)) < 0 ↔
      net.h H i * α ^ (-(net.Ms ℓ i : ℤ)) +
        ∑ k ∈ net.B i, net.h H k * α ^ (-(net.Ms ℓ k : ℤ)) < 0) := by sorry

end RoslingAssembly
