-- Prove2me | Theorems.Thm_StableVotingDistortion_gPhi_properties
-- name    : StableVotingDistortion.gPhi_properties
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:12.535221+00:00
-- url     : https://prove2.me/theorems/ef090c05-bc6a-4229-b203-69886f1f4ecb
-- title:
--   §6.3 — consequences of (26): $\phi(\lambda)=0$, and $g_\phi$ is an activation with $\phi=(1+\phi(0))(\tau-g_\phi)$
-- statement:
--   Let $\lambda\in(0,1)$ and let $\phi$ satisfy (26). Then:
--
--   1. $\phi(\lambda)=0$ and $\phi(r)\le0$ on $[\lambda,1]$;
--   2. $g_\phi(r)=(\phi(0)-\phi(r))/(1+\phi(0))$ is continuous and nondecreasing and maps $[0,1]$ into $[0,1]$;
--   3. $g_\phi(0)=0$ and $g_\phi(1)=1$;
--   4. with $\tau=\int_0^1g_\phi(r)\,dr$, we have $\phi=(1+\phi(0))(\tau-g_\phi)$ on $[0,1]$.
--
--   So $-\phi$ is a score function for the activation $g_\phi$.
--
--   Differences from the source:
--   - generalization: $g_\phi$ continuous and nondecreasing with $g_\phi(0)=0$, $g_\phi(1)=1$ → also `Set.MapsTo` $[0,1]$ into $[0,1]$, through `IsActivation (gPhi ϕ)`; reason: this follows from the printed clauses and Definition 3 requires it; dropping that clause gives the printed statement
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3, p.26

import Mathlib
import Definitions.Def_StableVotingDistortion_IsGStable
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives

set_option autoImplicit false

namespace StableVotingDistortion

/-- **Consequences of (26), §6.3.** `ϕ(λ) = 0` and `ϕ ≤ 0` on `[λ, 1]`; `g_ϕ` is continuous, nondecreasing,
maps `[0, 1]` into `[0, 1]`, has `g_ϕ(0) = 0` and `g_ϕ(1) = 1`; and `ϕ = (1 + ϕ(0))(τ − g_ϕ)` on `[0, 1]`,
where `τ = ∫_0^1 g_ϕ`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3, p.26: "In particular, these conditions imply that ϕ(λ) = 0 and ϕ(r) ≤ 0 on [λ, 1]. Reversing
Equation (23), the function g_ϕ(r) = (ϕ(0) − ϕ(r))/(1 + ϕ(0)) is continuous and nondecreasing with
g_ϕ(0) = 0 and g_ϕ(1) = 1, and satisfies ϕ = (1 + ϕ(0))(τ − g_ϕ) where τ = ∫_0^1 g_ϕ(r) dr."

**Formalization Note.** "Into `[0, 1]`" is not printed; it follows from the printed clauses and is what
Definition 3 needs. It is included through `IsActivation`. -/
theorem gPhi_properties {lam : ℝ} {ϕ : ℝ → ℝ} (h : IsScoreFunction lam ϕ) :
    ϕ lam = 0 ∧ (∀ r ∈ Set.Icc lam 1, ϕ r ≤ 0) ∧ IsActivation (gPhi ϕ) ∧
      gPhi ϕ 0 = 0 ∧ gPhi ϕ 1 = 1 ∧
      ∀ r ∈ Set.Icc (0 : ℝ) 1, ϕ r = (1 + ϕ 0) * ((∫ u in (0 : ℝ)..1, gPhi ϕ u) - gPhi ϕ r) := by sorry

end StableVotingDistortion
