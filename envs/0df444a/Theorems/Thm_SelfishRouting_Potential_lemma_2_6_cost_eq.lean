-- Prove2me | Theorems.Thm_SelfishRouting_Potential_lemma_2_6_cost_eq
-- name    : SelfishRouting.Potential.lemma_2_6_cost_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:12.417982+00:00
-- url     : https://prove2.me/theorems/e39e9ad1-d46a-44e1-a6c2-ed1f9f0e2d0f
-- title:
--   Lemma 2.6 (essential uniqueness) — all Nash flows have the same cost
-- statement:
--   Consider a routing instance with latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$, routes given by $0/1$ edge–route incidence columns, and positive rates $r_i$. Write $C(f)=\sum_P\ell_P(f)f_P$ for the cost of a flow.
--
--   **Lemma 2.6, second part.** If $f$ and $\tilde f$ are flows at Nash equilibrium, then
--   $$C(f)=C(\tilde f).$$
--
--   Nash flows need not be unique, but their cost is; this is what makes the ratio $\rho(G,r,\ell)=C(f)/C(f^*)$ of §2.5 independent of the choice of Nash flow.
--
--   **Formalization Note** Only the second sentence of Lemma 2.6 is formalized here; the first is `lemma_2_6_existence`. Routes are $0/1$ incidence columns, a generalization of simple paths; continuity and monotonicity are imposed on $[0,\infty)$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 9, Lemma 2.6 (second sentence)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Potential_Model

open KellyStochasticNetworks

namespace SelfishRouting.Potential

theorem lemma_2_6_cost_eq {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (rate : Fin Sd → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x x' : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x) (hx' : IsNashFlow A s ℓ rate x') :
    SelfishRouting.Bicriteria.cost A ℓ x = SelfishRouting.Bicriteria.cost A ℓ x' := by sorry

end SelfishRouting.Potential
