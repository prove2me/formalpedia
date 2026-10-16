-- Prove2me | Theorems.Thm_SensitivityPoA_Continuity_lemma_3
-- name    : SensitivityPoA.Continuity.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:58.015981+00:00
-- url     : https://prove2.me/theorems/d34cf642-c23d-449b-b3ad-f2277cdca1fa
-- title:
--   Lemma 3, p. 15 — positive optimum cost and bounds on the PoA
-- statement:
--   Let $\Gamma=(\tau,d)$ satisfy the game-space conditions, and let $f$, $\tilde f$, and $f^*$ be a feasible flow, a Wardrop equilibrium, and a social optimum. Every arc flow of $f$ lies in $[0,T(d)]$. With $|A|$ arcs and $|S|$ routes,
--   $$0<\frac{T(d)}{|S|}\min_{a\in A}\tau_a\!\left(\frac{T(d)}{|S|}\right)\le C(\Gamma,f^*)\le C(\Gamma,\tilde f)\le |A|T(d)\max_{a\in A}\tau_a(T(d)).$$
--   Consequently,
--   $$1\le\rho(\Gamma)\le\frac{|A||S|\max_{a\in A}\tau_a(T(d))}{\min_{a\in A}\tau_a(T(d)/|S|)}.$$
--   The positive lower bound makes the PoA quotient well defined throughout the game space.
--
--   **Formalization Note** The source's standing Condition 1 and the nonempty route and pair conditions are collected in the network predicate. Minima and maxima over arcs are represented by real infimum and supremum of finite nonempty ranges. The paper's displayed bound has the same constants.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 15, Lemma 3

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Continuity_Setting

namespace SensitivityPoA.Continuity

theorem lemma_3 (N : Network) (hN : N.Standing)
    (Γ : Game N) (hΓ : Γ ∈ gameSpace N)
    (f fwe fso : Fin N.R → ℝ)
    (hf : IsFlow Γ f) (hwe : IsWE Γ fwe) (hso : IsSO Γ fso) :
    (∀ j, 0 ≤ KellyStochasticNetworks.linkFlow N.A f j ∧ KellyStochasticNetworks.linkFlow N.A f j ≤ totalDemand Γ.d) ∧
    0 < totalDemand Γ.d / (N.R : ℝ) *
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) ∧
    totalDemand Γ.d / (N.R : ℝ) *
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) ≤ cost Γ fso ∧
    cost Γ fso ≤ cost Γ fwe ∧
    cost Γ fwe ≤ (N.J : ℝ) * totalDemand Γ.d *
      maxArc Γ (totalDemand Γ.d) ∧
    1 ≤ PoA Γ ∧
    PoA Γ ≤ (N.J : ℝ) * (N.R : ℝ) *
      maxArc Γ (totalDemand Γ.d) /
      minArc Γ (totalDemand Γ.d / (N.R : ℝ)) := by sorry

end SensitivityPoA.Continuity
