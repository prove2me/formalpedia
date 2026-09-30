-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_cor55i_strongly_monotone
-- name    : StochFictPlay.Supermodular.cor55i_strongly_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:22:32.219964+00:00
-- url     : https://prove2.me/theorems/a38c8306-ec46-49d0-947c-1f672687a474
-- title:
--   Corollary 5.5(i) — (P) is strongly monotone in the stochastic dominance order
-- statement:
--   Let $G$ be a strictly supermodular game with at least one strategy per player, in which two distinct players each have at least two strategies, and let the shock densities satisfy the conditions of Theorem 2.1. If $\{x_t\}_{t\ge0}$ and $\{y_t\}_{t\ge0}$ are solutions of (P) in $\Sigma$ with
--   $$T y_0 \ge T x_0 \quad\text{and}\quad y_0 \ne x_0,$$
--   then for every $t > 0$, $T y_t > T x_t$ strictly in every coordinate: $(T^\alpha y^\alpha_t)_i > (T^\alpha x^\alpha_t)_i$ for all $\alpha$ and $i$.
--
--   Strong monotonicity is what controls the limit sets of (P) and hence of stochastic fictitious play.
--
--   **Formalization Note** "$Ty_t > Tx_t$" is read as strict inequality in every coordinate, which is strong monotonicity in the sense of Smith (1995), the result the proof invokes. The assumption that two distinct players each have at least two strategies is the one under which Theorem 5.4 gives irreducibility; players with a single strategy are allowed.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 21, Corollary 5.5(i)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Dynamics

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Corollary 5.5(i) (Hofbauer–Sandholm 2002, manuscript p. 21). If `G` is strictly supermodular,
the dynamic `(P)` is strongly monotone with respect to the stochastic dominance order: if
`{x_t}` and `{y_t}` are solutions of `(P)` in `Σ` with `T y_0 ≥ T x_0` and `y_0 ≠ x_0`, then
`T y_t > T x_t` for all `t > 0`, strictly in every coordinate (strong monotonicity in the sense
of Smith 1995, which the proof invokes). The assumption that two distinct players each have at
least two strategies is the one under which Theorem 5.4 gives irreducibility; players with a single
strategy are allowed. -/
theorem cor55i_strongly_monotone {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (h2 : ∃ α β : Fin p, α ≠ β ∧ 2 ≤ n α ∧ 2 ≤ n β)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (x y : ℝ → Mixed n) (hx : IsSolution (pField f u) (mixedProfiles n) x)
    (hy : IsSolution (pField f u) (mixedProfiles n) y)
    (h0 : Tmap (x 0) ≤ Tmap (y 0)) (hne : y 0 ≠ x 0) :
    ∀ t : ℝ, 0 < t → ∀ (α : Fin p) (i : Fin (n α - 1)), Tco (x t α) i < Tco (y t α) i := by sorry

end StochFictPlay.Supermodular
