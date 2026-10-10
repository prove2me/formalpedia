-- Prove2me | Theorems.Thm_SDDiP_Envelope_g_eq_dual
-- name    : SDDiP.Envelope.g_eq_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:59.463589+00:00
-- url     : https://prove2.me/theorems/7ca27523-8eb5-4e7e-be41-494fd750672d
-- title:
--   Proof of Theorem 1, p. 496 — on $[0,1]^n$, (P) and (D) are solvable with equal values; $g(x)<\infty$
-- statement:
--   Let $f$ be a real function on $\{0,1\}^n$, let $\Pi$, $g$, $(P)$ and $(D)$ be as in the proof of Theorem 1, and let $x \in [0,1]^n$. Then the maximum of $(P)$ is attained, the minimum of $(D)$ is attained, and both equal $g(x)$:
--   $$g(x) = \max_{(\alpha,\beta)\in\Pi}\{\alpha^\top x + \beta\} = \min\Big\{\sum_{i=1}^N f(\hat x^i)\lambda_i : \hat X\lambda = x,\ e^\top\lambda = 1,\ \lambda \ge 0\Big\}.$$
--   In particular $g(x)$ is finite on $[0,1]^n$.
--
--   This is the linear programming duality step of the proof, stated for this pair of programs only; it gives finiteness of $g$ and is the bridge between the affine description of $g$ and convex combinations of binary points.
--
--   **Formalization Note** "Attained maximum equal to $g(x)$" is `IsGreatest (primalValues f x) (g f x)`, and likewise `IsLeast` for the dual objective values.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1, (P), (D) and 'the dual problem (D) is always feasible and bounded for any x ∈ C_n, which implies g(x) < ∞ for all x ∈ C_n'

import Mathlib
import Definitions.Def_SDDiP_Envelope_ProofLP

namespace SDDiP.Envelope

/-- Proof of Theorem 1, p. 496: for every `x ∈ Cₙ = [0,1]ⁿ` the linear program (P)
`max {xᵀα + β : (α, β) ∈ Π}` and its dual (D) `min {∑ᵢ f(x̂ⁱ) λᵢ : X̂λ = x, eᵀλ = 1, λ ≥ 0}` both attain
their optimum, and the optimal values agree; their common value is `g(x)`, which is therefore finite. -/
theorem g_eq_dual {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ cube n) :
    IsGreatest (primalValues f x) (g f x) ∧ IsLeast (dualValues f x) (g f x) := by sorry

end SDDiP.Envelope
