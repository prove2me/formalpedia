-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_prop53_linear_conjugacy
-- name    : StochFictPlay.Supermodular.prop53_linear_conjugacy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:21:15.830181+00:00
-- url     : https://prove2.me/theorems/8ecb2396-86d6-4e02-8555-296354a2c7ee
-- title:
--   Proposition 5.3 — (P) and (T) are linearly conjugate
-- statement:
--   Let $G$ be a finite normal form game with at least one strategy per player and let the shock densities satisfy the conditions of Theorem 2.1. For a curve $\{x_t\}_{t \ge 0}$ in $\Sigma$,
--   $$\{x_t\}_{t\ge0} \text{ solves (P) on } \Sigma \iff \{T x_t\}_{t \ge 0} \text{ solves (T) on } T(\Sigma).$$
--
--   The change of coordinates $T$ lets results about cooperative systems be applied to (P). No supermodularity is needed.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20, Proposition 5.3 (proof p. 31)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Dynamics

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Proposition 5.3 (Hofbauer–Sandholm 2002, manuscript p. 20). The dynamic `(P)` on `Σ` and the
dynamic `(T) v̇^α = T^α B̃^α((T^{−α})^{-1} v^{−α}) − v^α` on `T(Σ)` are linearly conjugate: a curve
`{x_t}_{t ≥ 0}` in `Σ` solves `(P)` if and only if `{T x_t}_{t ≥ 0}` solves `(T)`.
No supermodularity is needed; this is a change of coordinates. -/
theorem prop53_linear_conjugacy {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (γ : ℝ → Mixed n) (hγ : ∀ t : ℝ, 0 ≤ t → γ t ∈ mixedProfiles n) :
    IsSolution (pField f u) (mixedProfiles n) γ ↔
      IsSolution (gField f u) (TSigma n) (fun t => Tmap (γ t)) := by sorry

end StochFictPlay.Supermodular
