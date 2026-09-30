-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_thm51_pbr_monotone
-- name    : StochFictPlay.Supermodular.thm51_pbr_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:20:12.322299+00:00
-- url     : https://prove2.me/theorems/bdd3e671-c24a-4045-9fdc-01a17f242f9d
-- title:
--   Theorem 5.1 — perturbed best responses are monotone in the stochastic dominance order
-- statement:
--   Let $G$ be a strictly supermodular $p$ player game with at least one strategy per player, and let each player's shock density $f^\alpha$ satisfy the conditions of Theorem 2.1. Let $x, y \in \Sigma$ be mixed profiles and $\alpha$ a player. If the opponents' strategies in $y$ stochastically dominate those in $x$,
--   $$T^{-\alpha} y^{-\alpha} \ge T^{-\alpha} x^{-\alpha} \quad(\text{i.e. } T^\beta y^\beta \ge T^\beta x^\beta \text{ for all } \beta \ne \alpha),$$
--   then
--   $$T^\alpha \tilde B^\alpha(y^{-\alpha}) \ge T^\alpha \tilde B^\alpha(x^{-\alpha}).$$
--
--   This monotonicity of perturbed best responses is the basis of every result for supermodular games in the paper.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 19, Theorem 5.1 (proof pp. 28-29)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 5.1 (Hofbauer–Sandholm 2002, manuscript p. 19). Let `G` be a strictly supermodular
`p` player game whose players' shock densities `f α` meet the conditions of Theorem 2.1. If the
opponents' mixed strategies in `y` stochastically dominate those in `x`
(`T^{−α} y^{−α} ≥ T^{−α} x^{−α}`, i.e. `T^β x^β ≤ T^β y^β` for every `β ≠ α`), then player
`α`'s perturbed best responses are ordered the same way:
`T^α B̃^α(y^{−α}) ≥ T^α B̃^α(x^{−α})`. Player `α`'s own coordinates `x α`, `y α` do not enter
`B̃^α`. -/
theorem thm51_pbr_monotone {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (α : Fin p) (x y : Mixed n) (hx : x ∈ mixedProfiles n) (hy : y ∈ mixedProfiles n)
    (hxy : ∀ β : Fin p, β ≠ α → Tco (x β) ≤ Tco (y β)) :
    Tco (pbr f u x α) ≤ Tco (pbr f u y α) := by sorry

end StochFictPlay.Supermodular
