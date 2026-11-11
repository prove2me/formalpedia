-- Prove2me | Theorems.Thm_QaryCVP_appendix_F_2
-- name    : QaryCVP.appendix_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:16.131198+00:00
-- url     : https://prove2.me/theorems/99f9eb96-5bf7-44ed-ae64-38153fbd3714
-- title:
--   Appendix F.2 — the parameters (29) satisfy every constraint, $\max\{1/4,T_{\rm in},e\}<0.26675191$ and $\max\{1/8,S_{\rm in},e/2\}<0.262740033$
-- statement:
--   Take $k=3$, $(t_0,t_1,t_2,t_3)=(0.1135461,\,0.09917397,\,0.06690926,\,0.03531462)$, $\eta=10^{-8}$, $c=0.22711$, $a=4.138$, $\gamma=5/3$, $\rho=1$ and $\beta=2t_0$. Then:
--
--   1. the strict coordinate conditions $0<t_i<1/2$, $t_{i-1}/2<t_i<(1-t_{i-1})/2$ hold;
--   2. $h_0>1$;
--   3. the equation conditions (5), $1>d_1>d_2>d_3>0$, and the even-modulus conditions (8) hold;
--   4. $c>2t_0$;
--   5. the binary conditions (11): $0<\beta<1/4$ and $h(\beta)>3/4$;
--   6. the exact-search condition (22): $\Theta_u(a)\le\Theta(a)e^{-9au^2/25}$ for every $|u|\le1/2$;
--   7. the cost bounds
--
--   $$\max\{1/4,\ T_{\rm in},\ e(a,c,5/3)\}<0.26675191,\qquad\max\{1/8,\ S_{\rm in},\ e(a,c,5/3)/2\}<0.262740033.$$
--
--   This certificate fixes the constants $0.2668$ and $0.2628$ of Theorem 1.1.
--
--   **Formalization Note** The decimals are the exact rationals they denote. $\Theta$ is the full theta series and $\ln$, $\log_2$ are exact: a proof has to enclose these values rigorously.
--
--   Differences from the source: none.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Appendix F.2, pp.93–94; (29), p.43

import Mathlib
import Definitions.Def_QaryCVP_ent3

namespace QaryCVP

/-- **Appendix F.2** (verifying the selected parameters (29)). Kim, Kwon, Lee, Lee, STOC 2027
submission manuscript (sha256 9aeb2ff4…ab4), Appendix F.2, pp.93–94; (29), p.43; (11), p.33;
(22) and (24), p.41.

Take `k = 3`, `(t₀, t₁, t₂, t₃) = (0.1135461, 0.09917397, 0.06690926, 0.03531462)`, `η = 10⁻⁸`,
`c = 0.22711`, `a = 4.138`, `γ = 5/3`, `ρ = 1`, `β = 2t₀`. Then:

1. the strict coordinate conditions `0 < tᵢ < 1/2`, `tᵢ₋₁/2 < tᵢ < (1 − tᵢ₋₁)/2`;
2. the entropy surplus `h₀ > 1` (`h₀ > ρ` at `ρ = 1`);
3. the equation conditions (5), `1 > d₁ > d₂ > d₃ > 0`, and the even-modulus conditions (8);
4. the distance margin `c > 2t₀`;
5. the binary conditions (11), `0 < β < 1/4` and `h(β) > 3/4`;
6. the exact-search condition (22), `Θ_u(a) ≤ Θ(a)e^{−9au²/25}` for every `|u| ≤ 1/2`;
7. `max{1/4, T_in, e(a, c, 5/3)} < 0.26675191` and `max{1/8, S_in, e(a, c, 5/3)/2} < 0.262740033`.

**Formalization Note.** The decimals are the exact rationals they denote (p.43). `T_in`, `S_in` are
(9) at these parameters with `ρ = 1`, `Θ` is the full theta series (48), `ln`/`log₂` exact. -/
theorem appendix_F_2 :
    let t : ℕ → ℝ := fun i =>
      if i = 0 then 1135461 / 10 ^ 7 else if i = 1 then 9917397 / 10 ^ 8
      else if i = 2 then 6690926 / 10 ^ 8 else 3531462 / 10 ^ 8
    let η : ℝ := 1 / 10 ^ 8
    let c : ℝ := 22711 / 10 ^ 5
    let a : ℝ := 4138 / 1000
    StrictCoordCond 3 t ∧ 1 < hRate t 0 ∧ EqCond 3 1 η t ∧ ParityCond 3 1 η t ∧
      2 * t 0 < c ∧ (0 < 2 * t 0 ∧ 2 * t 0 < 1 / 4 ∧ 3 / 4 < binEnt (2 * t 0)) ∧
      ThetaCond (9 / 25) a ∧
      max (max (1 / 4) (Tin 3 1 η t)) (eCost a c (5 / 3)) < 26675191 / 10 ^ 8 ∧
      max (max (1 / 8) (Sin 3 1 η t)) (eCost a c (5 / 3) / 2) < 262740033 / 10 ^ 9 := by sorry

end QaryCVP
