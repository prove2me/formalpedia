-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_cor55ii_chainRecurrent_subset_interval
-- name    : StochFictPlay.Supermodular.cor55ii_chainRecurrent_subset_interval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:23:14.298521+00:00
-- url     : https://prove2.me/theorems/c5a53fb0-9e2f-47dc-96b2-568a6ca4ede5
-- title:
--   Corollary 5.5(ii) — the chain recurrent set lies between the minimal and maximal rest points
-- statement:
--   Let $G$ be a strictly supermodular game with at least one strategy per player, and let the shock densities satisfy the conditions of Theorem 2.1. Then:
--
--   1. If $\underline x, \bar x$ are rest points of (P) with $RP(P) \subseteq [\underline x, \bar x]$ (as provided by Theorem 5.2), then
--   $$CR(P) \subseteq [\underline x, \bar x].$$
--   2. In particular, if $RP(P) = \{x^*\}$, then $CR(P) = \{x^*\}$.
--
--   Since stochastic fictitious play converges to a connected chain recurrent set of (P), this confines its limit behavior.
--
--   **Formalization Note** Rest points with $RP(P) \subseteq [\underline x, \bar x]$ are exactly the minimal and maximal rest points, since $T$ is injective on $\Sigma$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 21, Corollary 5.5(ii) (proof p. 32)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Dynamics

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Corollary 5.5(ii) (Hofbauer–Sandholm 2002, manuscript p. 21; proof p. 32). If `G` is strictly
supermodular, the chain recurrent set of `(P)` lies between the minimal and maximal rest points:
for rest points `x̲, x̄` with `RP(P) ⊆ [x̲, x̄]` (those of Theorem 5.2), `CR(P) ⊆ [x̲, x̄]`. In
particular, if `RP(P) = {x*}`, then `CR(P) = {x*}` as well. -/
theorem cor55ii_chainRecurrent_subset_interval {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    (∀ xl xu : Mixed n, xl ∈ restPoints (pField f u) (mixedProfiles n) →
        xu ∈ restPoints (pField f u) (mixedProfiles n) →
        restPoints (pField f u) (mixedProfiles n) ⊆ orderInterval n xl xu →
        chainRecurrentSet (pField f u) (mixedProfiles n) ⊆ orderInterval n xl xu) ∧
    (∀ xs : Mixed n, restPoints (pField f u) (mixedProfiles n) = {xs} →
        chainRecurrentSet (pField f u) (mixedProfiles n) = {xs}) := by sorry

end StochFictPlay.Supermodular
