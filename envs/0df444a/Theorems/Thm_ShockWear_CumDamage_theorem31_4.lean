-- Prove2me | Theorems.Thm_ShockWear_CumDamage_theorem31_4
-- name    : ShockWear.CumDamage.theorem31_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:48:25.209162+00:00
-- url     : https://prove2.me/theorems/35d85f57-bfa6-4647-b175-f32689975066
-- title:
--   Theorem 3.1 (3.4) — $H$ is IHRA if $\bar P_k^{1/k}$ is decreasing in $k$
-- statement:
--   Let $\lambda > 0$ and let
--   $$\bar H(t) = \sum_{k=0}^\infty \bar P_k\, e^{-\lambda t}\frac{(\lambda t)^k}{k!}, \qquad t \ge 0,$$
--   where $1 = \bar P_0 \ge \bar P_1 \ge \dots \ge 0$. If $\bar P_k^{1/k}$ is decreasing in $k = 1, 2, \dots$, then $H$ is IHRA:
--   $$[\bar H(t)]^{1/t} \text{ is decreasing in } t > 0.$$
--
--   This is the discrete-to-continuous inheritance of the IHRA property under Poisson shocks: the condition on the $\bar P_k$ is the discrete analogue of the conclusion for $\bar H$.
--
--   **Formalization Note** $\bar P_k \ge 0$ (the $\bar P_k$ are probabilities) is stated explicitly. Powers are real powers. "Decreasing" is the weak sense.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 632, Theorem 3.1 (3.4)

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

theorem theorem31_4 (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k)
    (hroot : ∀ j k : ℕ, 1 ≤ j → j ≤ k → P k ^ (1 / (k : ℝ)) ≤ P j ^ (1 / (j : ℝ))) :
    IsIHRA (shockSurv lam P) := by sorry

end ShockWear.CumDamage
