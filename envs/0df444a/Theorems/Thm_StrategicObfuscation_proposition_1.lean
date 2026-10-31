-- Prove2me | Theorems.Thm_StrategicObfuscation_proposition_1
-- name    : StrategicObfuscation.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:06.727422+00:00
-- url     : https://prove2.me/theorems/8398bdce-bf00-4498-af11-9a3b65974d19
-- title:
--   Proposition 1 — the three kinds of equilibrium
-- statement:
--   Let $(e,\alpha,Q)$ be an equilibrium at $\sigma\in[0,1]$.
--
--   1. If $QV>c$, then $\alpha=1$ and $e=e(1,\sigma)$.
--   2. If $QV<c$, then $\alpha=0$ and $e=0$.
--   3. If $QV=c$, then $\alpha\in[0,1]$ satisfies
--
--   $$\frac{(1-\pi(\sigma,0))p}{(1-\pi(\sigma,0))p+(1-\pi(\sigma,e(\alpha,\sigma)))(1-p)}=\frac cV,\tag{4}$$
--
--   and $e=e(\alpha,\sigma)$.
--
--   This is the paper's taxonomy of equilibria: uncertified proposals are funded for sure, never, or at random.
--
--   Differences from the source:
--   - generalization: Assumption 1 with ∂²π/∂σ∂e < 0 for a twice differentiable π → IsDetection: monotonicity plus decreasing differences in σ, strict whenever π(σ,·) separates the two efforts; reason: the C² class satisfies it by integrating the mixed partial, and the paper's own example on p.14, which the strict form excludes, also satisfies it
--   - encoding: e(α, σ) written as a function → a fixed selection E with IsEffort π g E; reason: the argmax in (1) may not be a singleton; every selection is covered and existence of a maximizer stays part of the hypothesis, as in (1)
--   - encoding: Bayes' rule (2) as a quotient → (2) cross-multiplied in IsEquilibrium; reason: the same equation whenever the denominator is nonzero; at σ = 1, e = 0 the report is off path and a PBE leaves Q free, where Lean's 0/0 = 0 would pin it
--   - encoding: (4) as a quotient equal to c/V → (4) cross-multiplied (SolvesFour); reason: the same equation whenever the denominator is nonzero; it keeps a meaning at σ = 1
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Proposition 1, p.11

import Mathlib
import Definitions.Def_StrategicObfuscation_IsDetection
import Definitions.Def_StrategicObfuscation_IsEffort
import Definitions.Def_StrategicObfuscation_IsEquilibrium
import Definitions.Def_StrategicObfuscation_SolvesFour

open Set

namespace StrategicObfuscation

/-- **Proposition 1: the three kinds of equilibrium.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Proposition 1, p.11 (PDF p.11).

For an equilibrium `(e, α, Q)` at `σ`: if `Q V > c` then `α = 1` and `e = e(1, σ)`; if `Q V < c` then
`α = 0` and `e = 0`; if `Q V = c` then `α ∈ [0, 1]` solves (4) and `e = e(α, σ)`.

**Formalization Note** (4) is cross-multiplied (`SolvesFour`), so part 3 keeps its meaning at `σ = 1`.
-/
theorem proposition_1 {V c g p : ℝ} {π : ℝ → ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hc : 0 < c) (hcV : c < V) (hg : 0 < g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hπ : IsDetection π) (hE : IsEffort π g E)
    {σ e α Q : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (heq : IsEquilibrium π V c p E σ e α Q) :
    (c < Q * V → α = 1 ∧ e = E 1 σ) ∧
    (Q * V < c → α = 0 ∧ e = 0) ∧
    (Q * V = c → α ∈ Icc (0 : ℝ) 1 ∧ SolvesFour π V c p E σ α ∧ e = E α σ) := by sorry

end StrategicObfuscation
