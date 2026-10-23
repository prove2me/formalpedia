-- Prove2me | Theorems.Thm_PersPricingDist_UniformA_proposition_3
-- name    : PersPricingDist.UniformA.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T02:45:18.366329+00:00
-- url     : https://prove2.me/theorems/cc569d55-5b53-484b-96d8-a5c382d5b023
-- title:
--   Proposition 3, p. 12 — dual distribution is optimal with a uniform A price
-- statement:
--   Suppose consumers' valuations are positively correlated and A charges a uniform price. Whether B charges a uniform price or personalized prices, there is a nonnegative wholesale price at which the downstream game has an equilibrium, and every equilibrium at that wholesale price yields industry profit strictly above A's best mono-distribution profit:
--
--   $$\exists w_{UU}\ge0:\ \Pi_{UU}(w_{UU})>\Pi_U^m,\qquad \exists w_{UP}\ge0:\ \Pi_{UP}(w_{UP})>\Pi_U^m.$$
--
--   Thus dual distribution is the optimal distribution strategy under either pricing policy for B. **Formalization Note** The standing assumptions are $0<s<v<1$ and $X\ge v/s$. In UU, an equilibrium is a pair of global best responses; in UP, A is a price leader and B's per-consumer response is fixed by the paper's selected continuation. The statement requires at least one continuation equilibrium at each selected wholesale price and the strict gain at every such equilibrium; it compares with every uniform mono price.
-- source:
--   Jullien, Reisinger & Rey, Personalized Pricing and Distribution Strategies, authors' manuscript of March 2022 (Management Science, doi:10.1287/mnsc.2022.4437; PDF sha256 25a6c84ac0c48c6720f6a9e1f9b1f1ec516412c31dac044ac84c1d4c72dfc253), p. 12, Proposition 3 (PDF 14); proof OA pp. 1–4 (PDF 34–37)

import Mathlib
import Definitions.Def_PersPricingDist_UniformA_Setting

namespace PersPricingDist.UniformA

/-- Proposition 3, p. 12: under either retailer pricing policy, some
nonnegative wholesale price gives a nonempty continuation-equilibrium set, and
all equilibria at that price yield more industry profit than any uniform-price
mono-distribution outcome. -/
theorem proposition_3 (M : Model) (hM : M.Standing) :
    (∃ w : ℝ, 0 ≤ w ∧ (∃ pA pB : ℝ, M.IsNashUU w pA pB) ∧
      ∀ pA pB : ℝ, M.IsNashUU w pA pB →
        ∀ p : ℝ, M.monoProfitU p < M.indUU pA pB) ∧
    (∃ w : ℝ, 0 ≤ w ∧ (∃ pA : ℝ, M.IsLeaderOptUP w pA) ∧
      ∀ pA : ℝ, M.IsLeaderOptUP w pA →
        ∀ p : ℝ, M.monoProfitU p < M.indUP w pA) := by sorry
end PersPricingDist.UniformA
