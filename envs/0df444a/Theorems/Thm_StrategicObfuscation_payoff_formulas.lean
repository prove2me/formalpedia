-- Prove2me | Theorems.Thm_StrategicObfuscation_payoff_formulas
-- name    : StrategicObfuscation.payoff_formulas
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:27.893491+00:00
-- url     : https://prove2.me/theorems/02fa1e20-304d-4f39-b118-528707cddb96
-- title:
--   Proof of Proposition 2, p.28 — the payoff formulas for $\alpha^*<1$ and $\alpha^*=1$
-- statement:
--   Let $(e,\alpha,Q)$ be an equilibrium at $\sigma\in[0,1]$.
--
--   1. If $\alpha\in(0,1)$, then $QV=c$ and $(1-\pi(\sigma,0))p(V-c)=(1-p)(1-\pi(\sigma,e))c$.
--   2. If $\alpha<1$, then $u_S=p(V-c)\pi(\sigma,0)$.
--   3. If $\alpha=1$, then $u_S=pV-c+(1-p)\pi(\sigma,e)c$, where $e=e(1,\sigma)$.
--
--   So the sponsor's payoff depends on effort only when uncertified proposals are funded for sure.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), proof of Proposition 2, p.28

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_sponsorPayoff

open Set

namespace StrategicObfuscation

/-- **The sponsor's payoff in equilibrium.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), proof of Proposition 2, p.28 (PDF p.28).

In an equilibrium at `σ`: mixing `α ∈ (0, 1)` occurs only with `Q V = c`, equivalently
`(1 - π(σ, 0)) p (V - c) = (1 - p)(1 - π(σ, e)) c`; if `α < 1` then `u_S = p (V - c) π(σ, 0)`; and if
`α = 1` then `u_S = pV - c + (1 - p) π(σ, e) c`, where `e = e(1, σ)`. -/
theorem payoff_formulas {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    (0 < α → α < 1 →
      Q * V = c ∧ (1 - π σ 0) * p * (V - c) = (1 - p) * (1 - π σ e) * c) ∧
    (α < 1 → sponsorPayoff π V c p σ α e = p * (V - c) * π σ 0) ∧
    (α = 1 → sponsorPayoff π V c p σ α e = p * V - c + (1 - p) * π σ e * c) := by sorry

end StrategicObfuscation
