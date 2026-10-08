-- Prove2me | Theorems.Thm_SelfishRouting_Potential_lemma_2_2
-- name    : SelfishRouting.Potential.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:01.731434+00:00
-- url     : https://prove2.me/theorems/be48850d-f6dc-459d-93fb-ab318a20474d
-- title:
--   Lemma 2.2 — a feasible flow is at Nash equilibrium iff every used route is a minimum-latency route
-- statement:
--   Consider a routing instance: edges $e$ with latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$; routes $P$ given by $0/1$ edge–route incidence columns, each serving one commodity $i$ (the set $\mathcal P_i$); and positive rates $r_i$. For a flow $f$ write $\ell_P(f)=\sum_{e\in P}\ell_e(f_e)$ for the latency of route $P$.
--
--   **Lemma 2.2.** A flow $f$ feasible for the instance is at Nash equilibrium (Definition 2.1) if and only if, for every commodity $i$ and all $P_1,P_2\in\mathcal P_i$,
--   $$f_{P_1}>0\ \Longrightarrow\ \ell_{P_1}(f)\le\ell_{P_2}(f).$$
--
--   The right-hand side is the Wardrop condition: all routes of a commodity that carry flow have the same latency, and none is longer than an unused route. It is the form of the equilibrium used in every later argument of the paper.
--
--   **Formalization Note** The right-hand side is the published `KellyStochasticNetworks.IsWardropEquilibrium`, which includes feasibility, so both sides presuppose a feasible flow as the page does. Latency hypotheses are imposed on $[0,\infty)$ only, where flows live; continuity replaces the paper's differentiability, which footnote 3 (p. 7) allows. Routes are arbitrary $0/1$ incidence columns rather than simple paths, a disclosed generalization. Definition 2.1 is read with $P_1\ne P_2$ and $f_{P_1}>0$ (see the definition item).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 7, Lemma 2.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem lemma_2_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x : Fin R → ℝ) :
    IsNashFlow A s ℓ rate x ↔ IsWardropEquilibrium A s ℓ rate x := by sorry

end SelfishRouting.Potential
