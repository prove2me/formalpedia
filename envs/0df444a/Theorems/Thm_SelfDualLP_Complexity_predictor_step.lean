-- Prove2me | Theorems.Thm_SelfDualLP_Complexity_predictor_step
-- name    : SelfDualLP.Complexity.predictor_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:20.837964+00:00
-- url     : https://prove2.me/theorems/17c626d2-8358-487d-b98f-d76fbf9a48fb
-- title:
--   Proof of Theorem 6, predictor step — from $\mathcal N(1/4)$ into $\mathcal N(1/2)$ with $\theta^{k+1}/\theta^k\le1-8^{-1/4}/\sqrt{n+1}$
-- statement:
--   Work under the choice (7). Let $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)\in\mathcal N(1/4)$, let $d$ solve (11)–(12) at $z^k$ with $\gamma=0$, and let
--   $$
--   \bar\alpha=\max\{\alpha:\ z^k+\alpha d\in\mathcal N(1/2)\}
--   $$
--   be the step size (13), assumed to exist. Then $z^{k+1}=z^k+\bar\alpha d\in\mathcal N(1/2)$ and
--   $$
--   \frac{\theta^{k+1}}{\theta^k}=\frac{(x^{k+1})^Ts^{k+1}+\tau^{k+1}\kappa^{k+1}}{(x^k)^Ts^k+\tau^k\kappa^k}\le 1-\frac{8^{-1/4}}{\sqrt{n+1}} .
--   $$
--
--   Each predictor step therefore reduces the gap (and $\theta$) by a factor depending only on $n$.
--
--   **Formalization Note** The hypothesis that the maximum in (13) is attained is the paper's own presumption ("max"); the membership $z^{k+1}\in\mathcal N(1/2)$ is part of the claim as printed. Both ratios are stated, together with their equality.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6, predictor-step claim; (11)–(13) on p. 60

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_HLP
import Definitions.Def_SelfDualLP_Complexity_Neighborhood
import Definitions.Def_SelfDualLP_Complexity_PCSequence

open Matrix

namespace SelfDualLP.Complexity

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

end SelfDualLP.Complexity
