-- Prove2me | Theorems.Thm_SDDiP_Envelope_g_convex_piecewise_linear
-- name    : SDDiP.Envelope.g_convex_piecewise_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:35.104076+00:00
-- url     : https://prove2.me/theorems/8bbedd05-6874-47c2-bcc0-733ef7075238
-- title:
--   Proof of Theorem 1, p. 496 — $g$ is convex piecewise linear on $[0,1]^n$, with pieces at extreme points of $\Pi$
-- statement:
--   Let $f$ be a real function on $\{0,1\}^n$, and $\Pi$, $g$ as in the proof of Theorem 1. Then $g$ is convex on $C_n = [0,1]^n$, and there are finitely many extreme points $(\alpha_1,\beta_1), \dots, (\alpha_K,\beta_K)$ of the polyhedron $\Pi$ such that
--   $$g(x) = \max_{k=1,\dots,K}\big(\alpha_k^\top x + \beta_k\big) \qquad \text{for all } x \in [0,1]^n.$$
--
--   That is, $g$ is a convex piecewise linear function with a finite number of linear pieces, corresponding to extreme points of $\Pi$.
--
--   **Formalization Note** The maximum at $x$ is written as: each $\alpha_k^\top x + \beta_k \le g(x)$ and one of them equals $g(x)$. Extreme points are `Set.extremePoints ℝ` of $\Pi \subseteq \mathbb R^n \times \mathbb R$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1 ('Since Π is a polyhedron, g(x) is a convex piecewise linear function with a finite number of linear pieces, corresponding to extreme points of Π')

import Mathlib
import Definitions.Def_SDDiP_Envelope_ProofLP

namespace SDDiP.Envelope

/-- Proof of Theorem 1, p. 496: `g` is convex on `Cₙ = [0,1]ⁿ` and is there the maximum of finitely
many affine functions `x ↦ αₖᵀx + βₖ` whose coefficient pairs `(αₖ, βₖ)` are extreme points of the
polyhedron `Π` ("a convex piecewise linear function with a finite number of linear pieces,
corresponding to extreme points of `Π`"). -/
theorem g_convex_piecewise_linear {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    ConvexOn ℝ (cube n) (g f) ∧
    ∃ (K : ℕ) (α : Fin K → Fin n → ℝ) (β : Fin K → ℝ),
      (∀ k, (α k, β k) ∈ Set.extremePoints ℝ (PiPoly f)) ∧
      ∀ x ∈ cube n, (∀ k, α k ⬝ᵥ x + β k ≤ g f x) ∧ ∃ k, g f x = α k ⬝ᵥ x + β k := by sorry

end SDDiP.Envelope
