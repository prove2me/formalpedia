-- Prove2me | Theorems.Thm_StrategicObfuscation_posterior_le_prior
-- name    : StrategicObfuscation.posterior_le_prior
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:10.447048+00:00
-- url     : https://prove2.me/theorems/1168d627-f777-4186-a0ab-6ffc07749120
-- title:
--   §3 p.11 and proof of Proposition 1 p.26 — (3) is equivalent to $Q^*V>c$, and $Q^*\le p$
-- statement:
--   Let $\sigma\in[0,1)$ and let $(e,\alpha,Q)$ be an equilibrium at $\sigma$. Then $Q\le p$, and
--
--   $$QV>c\iff p(V-c)\,[1-\pi(\sigma,0)]>(1-p)\,c\,[1-\pi(\sigma,e)].$$
--
--   The right side is inequality (3): the benefit of funding an uncertified proposal exceeds its cost. The bound $Q\le p$ says that an uncertified report is bad news.
--
--   **Formalization Note** The statement is for $\sigma<1$; at $\sigma=1$ the report can be off path, and then $Q$ is free.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
--   - reading: (3) ⇔ Q*V > c and Q* ≤ p, for all σ → stated for σ < 1; reason: at σ = 1 with e = 0 the report is off path and Q is free, so neither claim can hold; the paper's Q* is only defined by (2) when its denominator is positive
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), eq. (3), p.11, and proof of Proposition 1, a.1, p.26

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium

open Set

namespace StrategicObfuscation

/-- **`Q* ≤ p`, and inequality (3) is equivalent to `Q* V > c`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), §3, eq. (3), p.11 (PDF p.11), and proof of Proposition 1,
a.1, p.26 (PDF p.26): "The benefit is larger than the cost if and only if
p(V − c)[1 − π(σ, 0)] > (1 − p)c[1 − π(σ, e∗)], (3) which is equivalent to Q∗V > c."

**Formalization Note** Stated for `σ < 1`. At `σ = 1` the report can be off path, and then `Q*` is
free. -/
theorem posterior_le_prior {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Ico (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    Q ≤ p ∧
    (c < Q * V ↔ (1 - p) * c * (1 - π σ e) < p * (V - c) * (1 - π σ 0)) := by sorry

end StrategicObfuscation
