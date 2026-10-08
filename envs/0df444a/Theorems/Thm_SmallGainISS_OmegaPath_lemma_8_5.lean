-- Prove2me | Theorems.Thm_SmallGainISS_OmegaPath_lemma_8_5
-- name    : SmallGainISS.OmegaPath.lemma_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:15:38.174175+00:00
-- url     : https://prove2.me/theorems/cc01fd1f-7a18-4bb8-b57e-533c40680c4d
-- title:
--   Lemma 8.5 — $(\mathrm{id}+\rho)^{-1}=\mathrm{id}-\tilde\rho$ with $\tilde\rho\in\mathcal K_\infty$
-- statement:
--   Let $\rho\in\mathcal K_\infty$. Then there exists $\tilde\rho\in\mathcal K_\infty$ such that
--   $$(\mathrm{id}+\rho)^{-1}=\mathrm{id}-\tilde\rho ,$$
--   where the inverse is the inverse function of $r\mapsto r+\rho(r)$ on $\mathbb R_+$.
--
--   The lemma lets one move a diagonal scaling $\mathrm{diag}(\mathrm{id}+\rho)$ from one side of an inequality to the other.
--
--   **Formalization Note** The statement also records $\tilde\rho(r)\le r$, so that $r-\tilde\rho(r)$ is ordinary subtraction (on `ℝ≥0` subtraction is truncated at $0$), and states the inverse as a two-sided inverse.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, p. 22, Lemma 8.5

import Mathlib
import Definitions.Def_SmallGainISS_OmegaPath_GainOperator

open scoped NNReal
open Filter Topology

namespace SmallGainISS.OmegaPath

/-- Lemma 8.5 (p. 22). For `ρ ∈ 𝒦∞` there is `ρ̃ ∈ 𝒦∞` with `(id + ρ)⁻¹ = id - ρ̃`: `ρ̃ ≤ id`
(so the subtraction is the real one) and `r ↦ r - ρ̃(r)` is the two-sided inverse of `r ↦ r + ρ(r)`. -/
theorem lemma_8_5 (ρ : ℝ≥0 → ℝ≥0) (hρ : SmallGainISS.Lyapunov.IsKInf ρ) :
    ∃ ρt : ℝ≥0 → ℝ≥0, SmallGainISS.Lyapunov.IsKInf ρt ∧ (∀ r, ρt r ≤ r) ∧
      Function.LeftInverse (fun r => r - ρt r) (fun r => r + ρ r) ∧
      Function.RightInverse (fun r => r - ρt r) (fun r => r + ρ r) := by sorry

end SmallGainISS.OmegaPath
