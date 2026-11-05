-- Prove2me | Theorems.Thm_RobustVolumeFlex_lookahead_peak_shaving_optimal
-- name    : RobustVolumeFlex.lookahead_peak_shaving_optimal
-- status  : Open
-- author  : @jorengijsbrechts
-- created : 2026-11-04T08:44:47.456423+00:00
-- url     : https://prove2.me/theorems/b4e18d1e-93eb-42d8-8110-84521974575c
-- title:
--   Theorem 1: the Lookahead Peak-Shaving policy is robustly optimal (with a no-end-effect condition)
-- statement:
--   Theorem 1 of Gijsbrechts et al. (2023): the Lookahead Peak-Shaving policy is robustly optimal, under one extra no-end-effect hypothesis.
--
--   Consider one period of the robust rolling-horizon model with volume flexibility, with data $h,b,c,c_p,x,(k_n)_{n<H},\Omega$ as in the definition `RobustVolumeFlex_Model`. Let $s=\lfloor c_p/h\rfloor$ be the lookahead horizon. Assume:
--
--   1. $h>0$, $c\ge 0$ and $k_n\ge 0$ for all $n$;
--   2. $\Omega$ is nonempty and bounded, and every $d\in\Omega$ has $d_i\ge 0$;
--   3. (Assumption 1) $h<c_p<b$;
--   4. (Assumption 2) $\lfloor c_p/h\rfloor<H$ and $\lfloor c/b\rfloor<H$;
--   5. (no end-of-horizon effect) $c+c_p\le b\,(H-s)$.
--
--   Then the linear program (4) has an optimal solution $(q,y,z)$ whose current-period order is the Lookahead Peak-Shaving order:
--   $$q_0=q^{\mathrm{LPS}}=\begin{cases}\hat S_0-x & x<\hat S_0-k_0,\\ k_0 & \hat S_0-k_0\le x<\hat S_0+\tau^s-k_0,\\ \hat S_0+\tau^s-x&\text{otherwise,}\end{cases}$$
--   where $\hat S_0$ is the uncapacitated base stock and $\tau^s$ the shifting need.
--
--   The theorem reduces the robust LP to an explicit two-threshold base-stock rule, the same structure as the stochastic optimum. It underlies the paper's closed-form policy parameters and sensitivity analysis.
--
--   **Formalization Note** Hypothesis 5 is not in the paper. Without it the statement fails: $H=2$, $h=1$, $c_p=1.5$, $b=2$, $c=3$, $x=0$, $k=(1,1)$, deterministic demand $(10,10)$ satisfies Assumptions 1–2, but the LP optimum orders 1 unit (cost 59), while LPS orders 10 (best follow-up cost 63.5). Hypothesis 1 and the conditions on $\Omega$ are the model's standing conventions. The conclusion is existential: ties may allow other optimal first-period orders.
-- source:
--   J. Gijsbrechts, C. Imdahl, R. N. Boute, J. A. Van Mieghem, Optimal robust inventory management with volume flexibility: Matching capacity and demand with the lookahead peak-shaving policy, Production and Operations Management 32 (2023) 3357-3373, https://doi.org/10.1111/poms.14069, p. 3365, Theorem 1 (with Assumption 1 p. 3364 and Assumption 2 p. 3365)

import Mathlib
import Definitions.Def_RobustVolumeFlex_Model

namespace RobustVolumeFlex

theorem lookahead_peak_shaving_optimal {H : ℕ} [NeZero H] (P : Params H)
    (h_pos : 0 < P.h) (c_nonneg : 0 ≤ P.c) (k_nonneg : ∀ n, 0 ≤ P.k n)
    (Ω_nonempty : P.Ω.Nonempty) (Ω_bounded : Bornology.IsBounded P.Ω)
    (demand_nonneg : ∀ d ∈ P.Ω, ∀ i, 0 ≤ d i)
    (assumption1 : P.h < P.cp ∧ P.cp < P.b)
    (assumption2 : ⌊P.cp / P.h⌋₊ < H ∧ ⌊P.c / P.b⌋₊ < H)
    (no_end_effect : P.c + P.cp ≤ P.b * ((H : ℝ) - ⌊P.cp / P.h⌋₊)) :
    ∃ q y z : Fin H → ℝ, IsRobustlyOptimal P q y z ∧ q 0 = lpsOrder P ⌊P.cp / P.h⌋₊ := by
  sorry

end RobustVolumeFlex
