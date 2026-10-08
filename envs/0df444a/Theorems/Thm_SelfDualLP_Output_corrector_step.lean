-- Prove2me | Theorems.Thm_SelfDualLP_Output_corrector_step
-- name    : SelfDualLP.Output.corrector_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:30.785304+00:00
-- url     : https://prove2.me/theorems/2b5f8979-bbf0-4928-a83b-59e27d28ad6c
-- title:
--   Proof of Theorem 6 — a corrector step from N(1/2) lands in N(1/4) and leaves θ unchanged
-- statement:
--   Work with (HLP) under the choice (7). Let $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)\in\mathcal N(1/2)$ and let $d$ solve the linear system (11)–(12) at $z^k$ with $\gamma=1$. Then $z^{k+1}=z^k+d$ lies in $\mathcal N(1/4)$ and
--
--   $$
--   \frac{\theta^{k+1}}{\theta^k}=\frac{(x^{k+1})^Ts^{k+1}+\tau^{k+1}\kappa^{k+1}}{(x^k)^Ts^k+\tau^k\kappa^k}=1.
--   $$
--
--   This is the corrector half of the Mizuno–Todd–Ye analysis: a full Newton step towards the central path restores the tighter neighborhood without changing the gap.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 62, proof of Theorem 6 (corrector-step claim); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 6, corrector-step claim (p. 62), under (7). Let `zᵏ ∈ 𝒩(1/2)` and let `d`
solve (11)–(12) at `zᵏ` with `γ = 1`. Then `zᵏ⁺¹ = zᵏ + d ∈ 𝒩(1/4)` and
`θᵏ⁺¹/θᵏ = ((xᵏ⁺¹)ᵀsᵏ⁺¹ + τᵏ⁺¹κᵏ⁺¹)/((xᵏ)ᵀsᵏ + τᵏκᵏ) = 1`. -/
theorem corrector_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z d : HLPPoint m n)
    (hz : Nbhd A b c (1 / 2) z) (hd : IsPCDirection A b c z d 1) :
    Nbhd A b c (1 / 4) (z.move d 1) ∧
    (z.move d 1).θ / z.θ = gap (z.move d 1) / gap z ∧
    gap (z.move d 1) / gap z = 1 := by sorry
end SelfDualLP.Output
