-- Prove2me | Theorems.Thm_SDDiP_Envelope_g_eq_f_binary
-- name    : SDDiP.Envelope.g_eq_f_binary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:25.439791+00:00
-- url     : https://prove2.me/theorems/7e5d7bf7-4ab8-4a95-b340-b80549b67162
-- title:
--   Proof of Theorem 1, p. 496 — $g(x) = f(x)$ at every binary point
-- statement:
--   Let $f$ be a real function on $\{0,1\}^n$ and $g(x) = \max_{(\alpha,\beta)\in\Pi}\{\alpha^\top x + \beta\}$ as in the proof of Theorem 1. For every binary point $x \in \{0,1\}^n$ the maximum defining $g(x)$ is attained and
--   $$g(x) = f(x).$$
--
--   This is the exactness half of Theorem 1 for the proof's function $g$; it fails for general finite sets in place of $\{0,1\}^n$.
--
--   **Formalization Note** The attained maximum is stated as `IsGreatest (primalValues f x) (f x)`.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 496, proof of Theorem 1 ('Therefore, g(x) = f(x) for all x ∈ {0, 1}^n')

import Mathlib
import Definitions.Def_SDDiP_Envelope_ProofLP

namespace SDDiP.Envelope

/-- Proof of Theorem 1, p. 496: `g(x) = f(x)` at every binary point `x ∈ {0,1}ⁿ`, where
`g(x) = max_{(α,β) ∈ Π} {αᵀx + β}`; the maximum is attained and equals `f(x)`. -/
theorem g_eq_f_binary {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ binaryPoints n) :
    IsGreatest (primalValues f x) (f x) ∧ g f x = f x := by sorry

end SDDiP.Envelope
