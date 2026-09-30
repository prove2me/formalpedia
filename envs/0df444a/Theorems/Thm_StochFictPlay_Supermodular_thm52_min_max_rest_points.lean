-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_thm52_min_max_rest_points
-- name    : StochFictPlay.Supermodular.thm52_min_max_rest_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:20:51.624351+00:00
-- url     : https://prove2.me/theorems/0008e6a4-67bb-4f7a-ad5e-1e2dc609abad
-- title:
--   Theorem 5.2 — minimal and maximal rest points of (P)
-- statement:
--   Let $G$ be a strictly supermodular game with at least one strategy per player, and let the shock densities satisfy the conditions of Theorem 2.1. Then the perturbed best response dynamic (P) has rest points $\underline x, \bar x \in RP(P)$ such that
--   $$RP(P) \subseteq [\underline x, \bar x] = \{x \in \Sigma : T\underline x \le T x \le T\bar x\}.$$
--
--   Rest points of (P) are approximate Nash equilibria of $G$; the theorem is the perturbed analogue of the existence of extremal equilibria in supermodular games.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20, Theorem 5.2 (proof p. 30)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Dynamics

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 5.2 (Hofbauer–Sandholm 2002, manuscript p. 20). In a strictly supermodular game whose
shock densities meet the conditions of Theorem 2.1, the perturbed best response dynamic
`(P) ẋ^α = B̃^α(x^{−α}) − x^α` on `Σ` has rest points `x̲` and `x̄` such that every rest point
lies in the order interval `[x̲, x̄] = {x ∈ Σ : T x̲ ≤ T x ≤ T x̄}`. -/
theorem thm52_min_max_rest_points {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    ∃ xl ∈ restPoints (pField f u) (mixedProfiles n),
      ∃ xu ∈ restPoints (pField f u) (mixedProfiles n),
        restPoints (pField f u) (mixedProfiles n) ⊆ orderInterval n xl xu := by sorry

end StochFictPlay.Supermodular
