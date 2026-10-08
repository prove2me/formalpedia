-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_lemma_2_2
-- name    : SelfishRouting.Bicriteria.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:25.396489+00:00
-- url     : https://prove2.me/theorems/d93f4f69-9138-4e6f-8116-c29b982a0030
-- title:
--   Lemma 2.2 — Nash flows are exactly the Wardrop equilibria
-- statement:
--   Consider an instance with edge–route incidence matrix $A$ (entries $0$ or $1$), commodities $i = 1,\dots,k$ with rates $r_i > 0$, routes $\mathcal P_i$ serving commodity $i$, and edge latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$. A flow $f$ is a Nash flow (Definition 2.1) if and only if it is feasible for $r$ and, for every $i$ and all $P_1, P_2 \in \mathcal P_i$ with $f_{P_1} > 0$,
--   $$
--   \ell_{P_1}(f) \le \ell_{P_2}(f).
--   $$
--
--   The right-hand side is the Wardrop condition: every route that carries flow has minimum latency among the routes of its commodity. The lemma is the working form of the equilibrium used in every later proof.
--
--   **Formalization Note.** The right-hand side is the published `KellyStochasticNetworks.IsWardropEquilibrium`, which includes feasibility; the page's "a flow $f$ feasible for instance $(G,r,\ell)$" is therefore on both sides. Routes are arbitrary $0/1$ incidence columns (a generalization of simple paths). The page assumes differentiable latencies; continuity replaces differentiability, as licensed by footnote 3 (p. 7) and §3 (p. 11), which strengthens the statement. Hypotheses on $\ell_e$ are imposed only on $[0,\infty)$, where edge flows live.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, Lemma 2.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Lemma 2.2 (p. 7): Definition 2.1 is equivalent to the Wardrop condition. -/
theorem lemma_2_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) :
    IsNashFlow A s ℓ rate x ↔ IsWardropEquilibrium A s ℓ rate x := by sorry

end SelfishRouting.Bicriteria
