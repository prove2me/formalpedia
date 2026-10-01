-- Prove2me | Theorems.Thm_ScenarioReduction_Redistribution_prescribed_redistribution
-- name    : ScenarioReduction.Redistribution.prescribed_redistribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:50:17.377793+00:00
-- url     : https://prove2.me/theorems/0c24b31c-de6e-433c-af73-fb21924236f5
-- title:
--   Theorem 3 (prescribed redistribution): D(J; q) ≤ Σ_{i∈J} p_i Σ_{j∉J} λ_j c(ω_i, ω_j), equality if #J = 1 and c satisfies the triangle inequality
-- statement:
--   Under the standing assumptions of Section 3, fix $J\subset\{1,\dots,N\}$ and redistribution weights $\lambda_j\ge0$, $j\notin J$, with $\sum_{j\notin J}\lambda_j=1$. Redistribute the deleted mass $p_J=\sum_{i\in J}p_i$ by the rule (12),
--
--   $$q_j=p_j+\lambda_jp_J\qquad(j\notin J).$$
--
--   Then
--
--   $$D(J;q)\le\sum_{i\in J}p_i\sum_{j\notin J}\lambda_jc(\omega_i,\omega_j).$$
--
--   Moreover, equality holds if $\#J=1$ and $c$ satisfies the triangle inequality $c(a,d)\le c(a,b)+c(b,d)$ for all $a,b,d\in\Omega$.
--
--   The theorem bounds the distance when the reduced weights are prescribed (for instance, to keep a uniform distribution uniform) instead of optimized as in Theorem 2.
--
--   **Formalization Note** $J$ may be empty; $\sum_{j\notin J}\lambda_j=1$ already forces at least one kept scenario. The triangle inequality is a hypothesis of the equality clause only, and is required on all of $\Omega$ as in the paper. Measurability, (C3) and (C4) are dropped as in the other items.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), p. 501, Theorem 3 and eq. (12)

import Mathlib
import Definitions.Def_ScenarioReduction_Redistribution_transportValue

open Finset

namespace ScenarioReduction.Redistribution

theorem prescribed_redistribution {Ω : Type*} {N : ℕ} (c : Ω → Ω → ℝ) (ω : Fin N → Ω) (p : Fin N → ℝ)
    (hc : ∀ a b : Ω, 0 ≤ c a b) (hc1 : ∀ a b : Ω, c a b = 0 ↔ a = b)
    (hc2 : ∀ a b : Ω, c a b = c b a)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (J : Finset (Fin N)) (lam : Fin N → ℝ) (hlam : ∀ j ∉ J, 0 ≤ lam j) (hlam1 : ∑ j ∈ Jᶜ, lam j = 1) :
    transportValue c ω p J (prescribedWeights p J lam) ≤ ∑ i ∈ J, p i * ∑ j ∈ Jᶜ, lam j * c (ω i) (ω j) ∧
      (J.card = 1 → (∀ a b d : Ω, c a d ≤ c a b + c b d) →
        transportValue c ω p J (prescribedWeights p J lam) = ∑ i ∈ J, p i * ∑ j ∈ Jᶜ, lam j * c (ω i) (ω j)) := by sorry

end ScenarioReduction.Redistribution
