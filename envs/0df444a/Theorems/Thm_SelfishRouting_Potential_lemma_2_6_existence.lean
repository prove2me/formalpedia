-- Prove2me | Theorems.Thm_SelfishRouting_Potential_lemma_2_6_existence
-- name    : SelfishRouting.Potential.lemma_2_6_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:13.308847+00:00
-- url     : https://prove2.me/theorems/edd26151-10ca-4f56-ada1-b3b934dcfd40
-- title:
--   Lemma 2.6 (existence) — an instance with continuous nondecreasing latencies admits a Nash flow
-- statement:
--   Consider a routing instance with latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$, routes given by $0/1$ edge–route incidence columns, and positive rates $r_i$, in which every commodity is served by at least one route.
--
--   **Lemma 2.6, first part.** The instance admits a feasible flow at Nash equilibrium:
--   $$\exists f\ \text{feasible with } f \text{ at Nash equilibrium (Definition 2.1)}.$$
--
--   Existence is what makes the efficiency ratio $\rho(G,r,\ell)$ of §2.5 well defined.
--
--   **Formalization Note** The hypothesis that every commodity is served by a route is the route-encoding reading of "an instance": in the paper each $\mathcal P_i$ is the nonempty set of $s_i$–$t_i$ paths, i.e. a feasible flow exists. Without it there is no feasible flow and the statement is false. Only the first sentence of Lemma 2.6 is formalized here; the second is `lemma_2_6_cost_eq`. Continuity and monotonicity are imposed on $[0,\infty)$ only. The published `KellyStochasticNetworks.wardrop_equilibrium_exists` is related work (global hypotheses, Wardrop condition).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 9, Lemma 2.6 (first sentence)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem lemma_2_6_existence {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (hserved : ∀ i, ∃ r, s r = i) :
    ∃ x : Fin R → ℝ, IsNashFlow A s ℓ rate x := by sorry

end SelfishRouting.Potential
