-- Prove2me | Theorems.Thm_PolyClinch_TwoSided_theorem_2_1
-- name    : PolyClinch.TwoSided.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:12.850508+00:00
-- url     : https://prove2.me/theorems/d62047e5-9c17-4d92-a333-0bc0be47a3e4
-- title:
--   Theorem 2.1, p. 5 — a mechanism with (ICb), (IRb), (IRs), (SBB) and (PO) exists (ε-grid of Assumption 3.2)
-- statement:
--   Fix a bipartite market $(N,M,E)$ with $n$ buyers and $m$ sellers and a clock step $\varepsilon>0$. There exists a mechanism $\mathcal M$, a map from public information to allocations, such that on every input whose bids $v'_i$ and reserve prices $\rho_j$ are nonnegative multiples of $\varepsilon$ (with nonnegative budgets and monotone submodular $f_j$):
--
--   1. $\mathcal M(\mathcal I)$ is an allocation: $w|_{E_j}\in P_j$ and $p_i\le B_i$;
--   2. (ICb) $u_i(\mathcal M(\mathcal I))\le u_i(\mathcal M(\mathcal I_i))$;
--   3. (IRb) $u_i(\mathcal M(\mathcal I_i))\ge0$;
--   4. (IRs) $u_j(\mathcal M(\mathcal I))\ge\rho_j f_j(E_j)$;
--   5. (SBB) $\sum_i p_i=\sum_j r_j$;
--   6. (PO) no allocation $\mathcal A$ with $\sum_i p_i\ge\sum_j r_j$ weakly improves $\mathcal M(\mathcal I^*)$ for all participants and strictly for one;
--
--   where in (ICb), (IRb) and (PO) the true valuations $v_i$ are nonnegative multiples of $\varepsilon$ as well.
--
--   This is the main result of Hirai and Sato: in budgeted two-sided markets with polymatroidal supply constraints, incentive compatibility for buyers, individual rationality on both sides, strong budget balance and Pareto optimality can be achieved together. Mechanisms 1 and 2 of §3 both witness it.
--
--   **Formalization Note** The restriction to the $\varepsilon$-grid is Assumption 3.2 (p. 10), under which the paper's mechanisms are analysed: it applies to bids, to reserve prices (the bids of the virtual buyers) and to true valuations (which become bids in $\mathcal I_i$ and $\mathcal I^*$). Budgets and the $f_j$ are not restricted. The graph is part of the input in the paper; choosing the mechanism for each graph is equivalent, since every property quantifies within one graph. Output feasibility is part of the page's definition of a mechanism (p. 4).
-- source:
--   Hirai & Sato, Polyhedral Clinching Auctions for Two-sided Markets, arXiv:1708.04881v2, p. 5, Theorem 2.1; p. 10, Assumption 3.2

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Market

namespace PolyClinch.TwoSided

/-- Theorem 2.1 (Hirai–Sato, arXiv:1708.04881v2, p. 5). For every bipartite market `E` and every
clock step `ε > 0`, there is a mechanism (a map from public information to allocations) that,
on every input whose bids and reserve prices are multiples of `ε` (Assumption 3.2, p. 10), outputs
an allocation and satisfies (ICb), (IRb), (IRs), (SBB) and (PO), the true valuations in (ICb),
(IRb) and (PO) being multiples of `ε` as well. -/
theorem theorem_2_1 (n m : ℕ) (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : Mechanism E, OutputsAllocations E ε M ∧ ICb E ε M ∧ IRb E ε M ∧ IRs E ε M ∧
      SBB E ε M ∧ PO E ε M := by sorry

end PolyClinch.TwoSided
