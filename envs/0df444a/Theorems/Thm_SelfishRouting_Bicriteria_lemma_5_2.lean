-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_lemma_5_2
-- name    : SelfishRouting.Bicriteria.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:14.040392+00:00
-- url     : https://prove2.me/theorems/833b15f8-6a82-4343-a8e6-f1312254b380
-- title:
--   Lemma 5.2 — $\epsilon$-approximate Nash flows are exactly the $(1+\epsilon)$-approximate Wardrop flows
-- statement:
--   Consider a routing instance with a $0/1$ edge–route incidence matrix, rates $r_i > 0$, and edge latency functions that are nonnegative, nondecreasing and continuous on $[0,\infty)$, and let $\epsilon > 0$. A flow $f$ is at $\epsilon$-approximate Nash equilibrium (Definition 5.1) if and only if it is feasible for $r$ and, for every commodity $i$ and all $P_1, P_2 \in \mathcal P_i$ with $f_{P_1} > 0$,
--   $$
--   \ell_{P_1}(f) \le (1+\epsilon)\,\ell_{P_2}(f).
--   $$
--
--   This is the analogue of Lemma 2.2 for approximate equilibria, and the form in which Theorem 5.3 uses the definition.
--
--   **Formalization Note.** The page's right-hand side has no feasibility clause, but Definition 5.1 presupposes a feasible flow; feasibility is included on both sides. $\epsilon > 0$ is the standing assumption of §5.1 (p. 19). Same model conventions as Lemma 2.2.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 19, Lemma 5.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Bicriteria_ApproxNash

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Lemma 5.2 (p. 19): Definition 5.1 is equivalent to the approximate Wardrop condition
`ℓ_{P₁}(f) ≤ (1 + ε) ℓ_{P₂}(f)` for every used route `P₁` and every route `P₂` of the
same commodity. -/
theorem lemma_5_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (ε : ℝ) (hε : 0 < ε) (x : Fin R → ℝ) :
    IsApproxNashFlow A s ℓ rate ε x ↔
      (x ∈ wardropFeasible s rate ∧
        ∀ r₁ r₂ : Fin R, s r₁ = s r₂ → 0 < x r₁ →
          pathLatency A ℓ x r₁ ≤ (1 + ε) * pathLatency A ℓ x r₂) := by sorry

end SelfishRouting.Bicriteria
