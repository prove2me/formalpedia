-- Prove2me | Theorems.Thm_StrategicObfuscation_no_obfuscation_equilibria
-- name    : StrategicObfuscation.no_obfuscation_equilibria
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:07.178016+00:00
-- url     : https://prove2.me/theorems/1d88d453-1518-43e7-923c-50ae2255c4b8
-- title:
--   Proof of Proposition 1, a.1–a.3, pp.26–27 — equilibria without obfuscation (corrected: a.2 concludes $e^*=0$, not $\alpha^*=0$)
-- statement:
--   Let $\sigma\in[0,1)$.
--
--   1. If $pV<c$, the unique equilibrium is $(e,\alpha,Q)=(0,0,p)$.
--   2. If $pV=c$, every equilibrium has $e=0$ and $Q=p$; and if $e(1,\sigma)=0$, then $(0,\alpha,p)$ is an equilibrium for every $\alpha\in[0,1]$.
--   3. If $pV>c$ and $e(1,\sigma)=0$, the unique equilibrium is $(0,1,p)$.
--
--   These are the regions of parameters where the applicant does not obfuscate.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
--   - correction: a.2: pV = c, σ > σ̄1 implies α* = 0 → pV = c implies e* = 0 and Q* = p, with α* free; reason: counterexample: π(σ,e) = σ exp(−e), g = 2, σ = 3/4, α = 2/3, pV = c; then e(α,σ) = 0 so (0, 2/3, p) is an equilibrium; α* > 0 does not force e* > 0
--   - reading: σ ≤ σ̄1 → E 1 σ = 0; reason: the appendix defines σ̄1(g) by e(1,σ,g) = 0 for all σ ≤ σ̄1(g); the Lean hypothesis is what the argument uses, and it covers every σ < σ̄1
--   - reading: a.1–a.3 for all σ → stated for σ < 1; reason: at σ = 1 the report can be off path and Q is free
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, a.1–a.3, pp.26–27

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium

open Set

namespace StrategicObfuscation

/-- **Equilibria without obfuscation, steps a.1–a.3 (a.2 corrected).**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), proof of Proposition 1, a.1–a.3, pp.26–27 (PDF pp.26–27).

For `σ < 1`:
* (a.1) if `pV < c`, then `(e, α, Q) = (0, 0, p)` is the unique equilibrium;
* (a.2) if `pV = c`, every equilibrium has `e = 0` and `Q = p`, and if `e(1, σ) = 0` then every
  `α ∈ [0, 1]` gives an equilibrium `(0, α, p)`;
* (a.3) if `pV > c` and `e(1, σ) = 0`, then `(e, α, Q) = (0, 1, p)` is the unique equilibrium.

**Formalization Note** The printed a.2 says that `pV = c`, `σ > σ̄1` force `α* = 0`, arguing that
`α* > 0` gives `e* > 0`. That step is false: for `π(σ, e) = σ exp(-e)`, `g = 2`, `σ = 3/4`, `α = 2/3`
one has `e(α, σ) = 0`, so `(0, 2/3, p)` is an equilibrium. The conclusion that survives is `e* = 0`,
`Q* = p` with `α*` free. The appendix defines `σ̄1(g)` by `e(1, σ, g) = 0` for all `σ ≤ σ̄1(g)`, so
"`σ ≤ σ̄1`" reads `E 1 σ = 0` here. -/
theorem no_obfuscation_equilibria {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ : ℝ} (hσ : σ ∈ Ico (0 : ℝ) 1) :
    (p * V < c → ∀ e α Q, IsEquilibrium π V c p E σ e α Q ↔ e = 0 ∧ α = 0 ∧ Q = p) ∧
    (p * V = c → ∀ e α Q, IsEquilibrium π V c p E σ e α Q → e = 0 ∧ Q = p) ∧
    (p * V = c → E 1 σ = 0 → ∀ α ∈ Icc (0 : ℝ) 1, IsEquilibrium π V c p E σ 0 α p) ∧
    (c < p * V → E 1 σ = 0 →
      ∀ e α Q, IsEquilibrium π V c p E σ e α Q ↔ e = 0 ∧ α = 1 ∧ Q = p) := by sorry

end StrategicObfuscation
