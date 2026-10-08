-- Prove2me | Theorems.Thm_PriceOfStability_Undirected_three_node_instance
-- name    : PriceOfStability.Undirected.three_node_instance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:22.205502+00:00
-- url     : https://prove2.me/theorems/47b46422-4a22-4aae-940c-896ae0a328e6
-- title:
--   Sect. 4 example — cheapest Nash equilibrium costs 4, optimum costs $3+\varepsilon$
-- statement:
--   In the 3-node example of Section 4 (nodes $s,t_1,t_2$; edges $(s,t_1)$, $(s,t_2)$ of cost $2$ and $(t_1,t_2)$ of cost $1+\varepsilon$; player $i$ connects $t_i$ with $s$), let $0<\varepsilon<1$. Then:
--
--   1. some pure Nash equilibrium has total cost $4$, and every pure Nash equilibrium has total cost at least $4$;
--   2. some profile has total cost $3+\varepsilon$, and every profile has total cost at least $3+\varepsilon$.
--
--   Hence the price of stability of this instance is $$\frac{4}{3+\varepsilon}\ \longrightarrow\ \frac43\qquad(\varepsilon\to0),$$ so the bound of Claim 4.1 is tight.
--
--   **Formalization Note.** The paper leaves the range of $\varepsilon$ implicit: $\varepsilon>0$ keeps the trees of cost $3+\varepsilon$ from being equilibria, and $\varepsilon<1$ makes $3+\varepsilon<4$.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Sect. 4, example before Claim 4.1

import Definitions.Def_PriceOfStability_Undirected_ThreeNode
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- The 3-node example of Sect. 4 (Anshelevich et al., SIAM J. Comput. 38 (2008), p. 1613,
PDF p. 12): for `0 < ε < 1`, "the optimal centralized solution has cost `3 + ε`. However, the
cheapest Nash has cost `4`." That is: some pure Nash equilibrium costs `4` and every one costs at
least `4`; some profile costs `3 + ε` and every profile costs at least `3 + ε`. The ratio
`4/(3 + ε)` tends to `4/3` as `ε → 0`.

**Formalization Note.** The paper leaves the range of `ε` implicit; `0 < ε` is needed for the
`3 + ε` trees not to be equilibria, and `ε < 1` for `3 + ε < 4`. -/
theorem three_node_instance (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
    (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
    (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
    (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P) := by sorry

end PriceOfStability.Undirected
