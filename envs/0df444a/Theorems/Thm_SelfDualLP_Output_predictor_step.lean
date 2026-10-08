-- Prove2me | Theorems.Thm_SelfDualLP_Output_predictor_step
-- name    : SelfDualLP.Output.predictor_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:30.072235+00:00
-- url     : https://prove2.me/theorems/f2e5754e-9d16-4d1f-9789-94f767d7ce9d
-- title:
--   Proof of Theorem 6 — a predictor step from N(1/4) lands in N(1/2) and shrinks θ by 1 − 8^{−1/4}/√(n+1)
-- statement:
--   Work with (HLP) under the choice (7). Let $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)\in\mathcal N(1/4)$, let $d$ solve the linear system (11)–(12) at $z^k$ with $\gamma=0$, and let
--
--   $$\bar\alpha=\max\{\alpha : z^k+\alpha d\in\mathcal N(1/2)\}$$
--
--   (assumed to be attained). Then $z^{k+1}=z^k+\bar\alpha d$ lies in $\mathcal N(1/2)$ and
--
--   $$
--   \frac{\theta^{k+1}}{\theta^k}=\frac{(x^{k+1})^Ts^{k+1}+\tau^{k+1}\kappa^{k+1}}{(x^k)^Ts^k+\tau^k\kappa^k}\le 1-\frac{8^{-1/4}}{\sqrt{n+1}}.
--   $$
--
--   This is the predictor half of the Mizuno–Todd–Ye analysis applied to (HLP). It guarantees that each predictor step keeps the iterate near the central path and reduces $\theta$ by a fixed factor.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6 (predictor-step claim); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 6, predictor-step claim (p. 62), under (7). Let `zᵏ ∈ 𝒩(1/4)`, let `d`
solve (11)–(12) at `zᵏ` with `γ = 0`, and let `ᾱ = max {α : zᵏ + αd ∈ 𝒩(1/2)}` (13) (assumed
attained). Then `zᵏ⁺¹ = zᵏ + ᾱd ∈ 𝒩(1/2)` and
`θᵏ⁺¹/θᵏ = ((xᵏ⁺¹)ᵀsᵏ⁺¹ + τᵏ⁺¹κᵏ⁺¹)/((xᵏ)ᵀsᵏ + τᵏκᵏ) ≤ 1 − 8^{−1/4}/√(n + 1)`. -/
theorem predictor_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z d : HLPPoint m n) (αbar : ℝ)
    (hz : Nbhd A b c (1 / 4) z) (hd : IsPCDirection A b c z d 0)
    (hα : IsGreatest {a : ℝ | Nbhd A b c (1 / 2) (z.move d a)} αbar) :
    Nbhd A b c (1 / 2) (z.move d αbar) ∧
    (z.move d αbar).θ / z.θ = gap (z.move d αbar) / gap z ∧
    gap (z.move d αbar) / gap z ≤ 1 - (8 : ℝ) ^ (-(1 / 4 : ℝ)) / Real.sqrt ((n : ℝ) + 1) := by sorry
end SelfDualLP.Output
