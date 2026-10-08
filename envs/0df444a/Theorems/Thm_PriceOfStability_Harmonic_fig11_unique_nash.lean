-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_fig11_unique_nash
-- name    : PriceOfStability.Harmonic.fig11_unique_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:01:45.613993+00:00
-- url     : https://prove2.me/theorems/36479fe0-30de-42ed-a85e-38e4ee48c2e2
-- title:
--   Fig. 1.1 — the unique Nash equilibrium costs H(k) while a profile costs 1 + ε
-- statement:
--   Let $k\ge1$ and $\varepsilon>0$, and consider the instance of Fig. 1.1: player $i$ ($1\le i\le k$) connects a common source $s$ to its terminal $t_i$ either by its own edge of cost $1/i$ or by a common edge of cost $1+\varepsilon$ followed by a private edge of cost $0$, with Shapley cost sharing. Then
--
--   1. the game has exactly one pure Nash equilibrium;
--   2. every pure Nash equilibrium has total cost $\sum_{i=1}^k 1/i=H(k)$;
--   3. the profile in which all players use the common path costs $1+\varepsilon$.
--
--   Hence the price of stability of this instance is at least $H(k)/(1+\varepsilon)$, which tends to $H(k)$ as $\varepsilon\to0$: the bound of Theorem 2.1 is tight.
--
--   **Formalization Note.** The paper calls the all-common profile optimal; that is false for $k=1$ (the own edge costs $1<1+\varepsilon$), so only the existence of a profile of cost $1+\varepsilon$ is stated.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1604 (PDF p. 3), Fig. 1.1 and the preceding paragraph; p. 1608 (PDF p. 7)

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Sect. 1, p. 1604 (PDF p. 3), Fig. 1.1: with `k ≥ 1` players and `ε > 0`, the instance
of Fig. 1.1 has a unique Nash equilibrium, it costs `H(k) = Σ_{i=1}^k 1/i`, and the profile in
which all players share the common path costs `1 + ε`. Hence the price of stability of this
instance is at least `H(k)/(1 + ε)`, which tends to `H(k)` as `ε → 0` (caption of Fig. 1.1;
"the upper bound of Theorem 2.1 is tight", p. 1608).

**Formalization Note.** The second conjunct is implied by the first together with the
computation of the equilibrium's cost; it is stated separately because it is the claim of the
page. The page's "the optimal solution … for a total cost of 1 + ε" is false for `k = 1`
(the own edge costs `1 < 1 + ε`), so only the existence of a profile of cost `1 + ε` is stated. -/
theorem fig11_unique_nash (k : ℕ) (ε : ℝ) (hk : 1 ≤ k) (hε : 0 < ε) :
    (∃! S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε := by sorry

end PriceOfStability.Harmonic
