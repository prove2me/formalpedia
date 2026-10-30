-- Prove2me | Theorems.Thm_RoslingAssembly_total_lead_succ
-- name    : RoslingAssembly.total_lead_succ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:48.678234+00:00
-- url     : https://prove2.me/theorems/57acec2b-3acf-4ac6-891a-7349a9eb264a
-- title:
--   Total lead time recursion $M_i=l_i+M_{s(i)}$
-- statement:
--   In every assembly network with lead times $l$, the total lead time of every item $i$ is its own lead time plus the total lead time of its immediate successor:
--   $$M_i=l_i+M_{s(i)},\qquad M_{s(1)}=M_0=0 .$$
--
--   This turns the exponents $l_k-(M_k-M_i)$ in the cost computation of the proof of Theorem 4(i) into $-(M_{s(k)}-M_{s(i)})+l_i$.
--
--   **Formalization Note** Items are `Fin N`, 0-based; $M_i$ is defined by its sum over all successors.
--
--   Differences from the source:
--   - generalization: the items are indexed so that M_i ≥ M_{i−1} for all i (p. 567) → not assumed; only the clause k < i for k ∈ A(i) is kept (`Network.s_lt`); reason: the clause is never used; every tree has such an indexing and the statement is invariant under reindexing, so the Lean statement specializes to the paper's
--   - encoding: items 1, …, N, end item 1, s(1) = 0, M_0 = 0 → items `Fin N`, 0-based, end item 0, `s 0 = none`, `Ms 0 = 0`; reason: renaming of indices; same instances
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §2, p. 567 (unnumbered, from the definition of M_i)

import Mathlib
import Definitions.Def_RoslingAssembly_Network_Ms

namespace RoslingAssembly

/-- **Recursion for the total lead time**, M_i = l_i + M_{s(i)} (§2, p. 567, unnumbered).
Rosling, *Optimal Inventory Policies for Assembly Systems under Random Demands*, Operations
Research 37(4), 1989, §2, p. 567: "M_i = total lead-time for item i and all its successors;
M_0 = 0 and M_i = l_i + Σ_{k∈A(i)} l_k for i = 1, 2, . . . N."

For every assembly network and lead times `ℓ`, the total lead time of each item is its own lead
time plus the total lead time of its immediate successor (`0` for the end item).

**Formalization Note.** Items are `Fin N`, 0-based; `Ms` is the paper's `M_{s(i)}` with
`M_{s(1)} = M_0 = 0`. -/
theorem total_lead_succ {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) :
    net.M ℓ i = ℓ i + net.Ms ℓ i := by sorry

end RoslingAssembly
