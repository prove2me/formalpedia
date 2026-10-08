-- Prove2me | Theorems.Thm_SelfDualLP_Output_kappa_upper_bound
-- name    : SelfDualLP.Output.kappa_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:27:43.323235+00:00
-- url     : https://prove2.me/theorems/4558a404-babc-4f51-ad6e-fdb223b628d3
-- title:
--   Proof of Theorem 8 — κᵏ ≤ (n + 1) + (n + 1)θᵏ ≤ 2(n + 1) for all k
-- statement:
--   Work with (HLP) under the choice (7) and let $(z^k)_{k\ge0}$, $z^k=(y^k,x^k,\tau^k,\theta^k,s^k,\kappa^k)$, be a predictor–corrector sequence. Then for every $k$
--
--   $$
--   \kappa^k\le(n+1)+(n+1)\theta^k\le 2(n+1).
--   $$
--
--   This follows the paper's remark "from relation (9)"; it is the upper bound on $\kappa^k$ behind the leftmost inequality $(1-2\beta)/(2(n+1))\le(1-2\beta)/\kappa^k$ of Theorem 8.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 63, proof of Theorem 8 (last sentence); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Complexity_LPData
import Definitions.Def_SelfDualLP_Output_HLP
import Definitions.Def_SelfDualLP_Output_Neighborhood
import Definitions.Def_SelfDualLP_Output_PCSequence

open Matrix

namespace SelfDualLP.Output

/-- Proof of Theorem 8 (p. 63): along every predictor–corrector sequence, relation (9) gives
`κᵏ ≤ (n + 1) + (n + 1)θᵏ ≤ 2(n + 1)` for all `k`. -/
theorem kappa_upper_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z : ℕ → HLPPoint m n) (hz : IsPCSequence A b c z) :
    ∀ k, (z k).κ ≤ ((n : ℝ) + 1) + ((n : ℝ) + 1) * (z k).θ ∧
      ((n : ℝ) + 1) + ((n : ℝ) + 1) * (z k).θ ≤ 2 * ((n : ℝ) + 1) := by sorry
end SelfDualLP.Output
