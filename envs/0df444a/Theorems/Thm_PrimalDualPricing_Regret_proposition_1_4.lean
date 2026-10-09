-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_proposition_1_4
-- name    : PrimalDualPricing.Regret.proposition_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:47.399985+00:00
-- url     : https://prove2.me/theorems/0ef88591-abd0-403d-badc-ea80fe7f6356
-- title:
--   Proposition 1.4, p. 6 — the constant price $p^*_m=\mathcal P_m(z^*)$ solves the fluid problem, with complementary slackness
-- statement:
--   Let the demand functions satisfy Assumption 1, let $z^*=\operatorname{argmin}_{z\ge0}g(z)$ with $g(z)=cz+T\sum_m\mathcal R_m(z)$, and let $p^*_m=\mathcal P_m(z^*)$. Then:
--   1. the constant path $p_m(t)\equiv p^*_m$ is feasible for the fluid problem (2);
--   2. it is optimal:
--   $$J^D(T,c)=T\sum_{m=1}^M p^*_m\,d_m(p^*_m);$$
--   3. complementary slackness holds:
--   $$z^*\Big(c-T\sum_{m=1}^M d_m(\mathcal P_m(z^*))\Big)=0;$$
--   4. consequently, for every $n$, the scaled fluid value is $J^D_n(T,c)=n\,T\sum_m p^*_m d_m(p^*_m)$.
--
--   This identifies the benchmark in the regret $R^\pi_n=1-J^\pi_n/J^D_n$. It also shows that the learning target is the vector of constant prices $p^*$, determined by the scalar dual optimum $z^*$.
--
--   **Formalization Note** The fluid value $J^D$ is the supremum of (2) over measurable price paths with values in $[0,p_\infty]$. Part 4 is the scaling remark of p. 7 applied to parts 1–2.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 6, Proposition 1, part 4; p. 7 (J^D_n scales linearly in n)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Model
import Definitions.Def_PrimalDualPricing_Regret_FluidValue

namespace PrimalDualPricing.Regret

/-- Proposition 1.4 (Chen–Gallego, arXiv:1812.09234v3, p. 6), under Assumption 1 (`Model`): with
`z* = argmin_{z ≥ 0} g(z)` and `p*_m = 𝒫_m(z*)`, the constant path `p_m(t) ≡ p*_m` is an optimal solution of
the fluid problem (2) — it is feasible and attains `J^D(T, c) = T ∑_m p*_m d_m(p*_m)` — and complementary
slackness `z*(c − T ∑_m d_m(𝒫_m(z*))) = 0` holds. Consequently, in the `n`-th system (demand `n d_m`,
inventory `n c`), `J^D_n(T, c) = n T ∑_m p*_m d_m(p*_m)`. -/
theorem proposition_1_4 {M : ℕ} (μ : Model M) :
    FluidFeasible μ.d μ.pinf μ.c μ.T (fun _ m => μ.pstar m) ∧
    fluidValue μ.d μ.pinf μ.c μ.T = μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m) ∧
    μ.zstar * (μ.c - μ.T * ∑ m, μ.d m (μ.P m μ.zstar)) = 0 ∧
    ∀ n : ℕ, fluidValueN μ.d μ.pinf μ.c μ.T n
      = (n : ℝ) * (μ.T * ∑ m, μ.pstar m * μ.d m (μ.pstar m)) := by sorry

end PrimalDualPricing.Regret
