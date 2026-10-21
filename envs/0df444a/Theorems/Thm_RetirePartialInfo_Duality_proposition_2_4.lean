-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_proposition_2_4
-- name    : RetirePartialInfo.Duality.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:23.786607+00:00
-- url     : https://prove2.me/theorems/46c18a17-b9c1-4835-9f6f-33d6da1ec777
-- title:
--   Proposition 2.4, p. 13 (verification clause) — a dual multiplier and dual-optimal retirement time meeting the budget give an optimal plan; no duality gap
-- statement:
--   Consider the consumption–investment–retirement problem of the mission: an agent who observes only the stock price (filtration $\mathcal F^S$), with labour income $\xi$ until retirement, utility cost of labour $\ell$, mandatory retirement at $T_1$, utilities $U_1,U_2$, primal values $V(0,x,0)$, $V(0,x,1)$ and dual values $\mathbf L(0,y,0)$, $\mathbf L(0,y,1)$. Assume the set-up of §2.1, Assumptions 2.1, 2.2 (for $U_1$ and $U_2$) and 2.3 (at $t=0$), and the dual integrability condition. Write $c^*_s=I_1(s,y^*_s)$, $H^*=I_2(T,y^*_T)$, $R^*_s=\mathbf 1\{s\ge\hat\tau\}$.
--
--   1. **Working agent** ($R_0=0$). Let $x>b(0)$ and $y^*>0$, and let $\hat\tau$ be an $\mathcal F^S$-stopping time in $[0,T_1]$ that is optimal in (14) at $y^*$ and satisfies $\mathcal X(0,y^*)=x-b(0)$ (21). Then there is a wealth process $H$ with $H_T=H^*$ such that $(c^*,H,R^*)\in\mathcal B(x)$, the plan is optimal for (10), and
--   $$V(0,x,0)=\inf_{y>0}\bigl\{\mathbf L(0,y,0)+y(x-b(0))\bigr\}=\mathbf L(0,y^*,0)+y^*(x-b(0)),$$
--   the infimum being attained (a minimum) and the supremum $V(0,x,0)$ attained by $(c^*,H,R^*)$.
--   2. **Retired agent** ($R_0=1$). Let $x>0$ and $y^*>0$ with $\mathcal X_1(0,y^*)+\mathcal X_2(0,y^*)=x$. Then there is $H$ with $H_T=H^*$ and $(c^*,H)\in\mathcal B_1(x)$, the pair is optimal for (12), and
--   $$V(0,x,1)=\inf_{y>0}\bigl\{\mathbf L(0,y,1)+yx\bigr\}=\mathbf L(0,y^*,1)+y^*x.$$
--
--   The theorem says that the primal optimal retirement problem under partial information is solved by solving the dual optimal stopping problem and the budget equation (21): once a dual multiplier and a dual-optimal retirement time meet the budget, the plan they define is optimal and there is no duality gap.
--
--   **Formalization Note.** This is the verification clause of Proposition 2.4. The printed proposition also asserts that such a $y^*$ exists; that existence clause is false in general (with $\theta\equiv0$ and $\beta>r$ the budget cost $\mathcal X(0,\cdot)$ jumps down by $-b(0)>0$ at one multiplier, so some wealth levels $x>b(0)$ admit no $y^*$; see the mission description) and is not posed. The paper's proof begins "Suppose that such a $y^*$ exists", and p. 14 reads the result as holding for "the solution of the duality approach, if it exists". Posed at $t=0$, where $\mathcal F^S_0$ is trivial and $V$, $\mathbf L$, $\mathcal X$ are numbers. The paper's $\hat\tau_{0,y^*}$ is replaced by any optimal stopping time of (14) at $y^*$. The conclusions are stated as greatest and least elements of the sets of primal and dual values, so that no supremum or infimum of an unbounded or empty set enters; $V(0,x,R_0)$ is the supremum of the primal values.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 13, Proposition 2.4

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Proposition 2.4**, p. 13 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 13, Proposition 2.4), **verification clause**, at
`t = 0`: "Using the `y*`, the triplet `(c*, H*, R*)` defined in (18) is the optimal solution to the
primal problem (10). In addition, the `y*` solves the dual problem:
`V(t, x_t, R_t) = inf_{y>0}{𝐋(t, y, R_t) + y(x_t − b(t)(1 − R_t))} = 𝐋(t, y*, R_t) + y*(x_t − b(t)(1 − R_t))`."

1. **Working agent** (`R_0 = 0`). Let `x > b(0)`, `y* > 0`, and let `τ̂` be an `F^S`-stopping time
   in `[0, T1]` that is optimal in (14) at `y*` and satisfies (21), `𝒳(0, y*) = x − b(0)`. Then
   there is a wealth process `H` with `H_T = I_2(T, y*_T)` such that `(c*, H, R*) ∈ ℬ(x)`; its
   objective is the greatest element of the objectives over `ℬ(x)` and equals `V(0, x, 0)`; it is
   the least element of `{𝐋(0, y, 0) + y(x − b(0)) : y > 0}`, attained at `y*`.
2. **Retired agent** (`R_0 = 1`). Let `x > 0`, `y* > 0` with `𝒳_1(0, y*) + 𝒳_2(0, y*) = x`. Then
   there is `H` with `H_T = I_2(T, y*_T)` and `(c*, H) ∈ ℬ_1(x)`; its objective (12) is the
   greatest over `ℬ_1(x)` and equals `V(0, x, 1)`; it is the least element of
   `{𝐋(0, y, 1) + yx : y > 0}`, attained at `y*`.

**Formalization Note.** This is the verification clause of Proposition 2.4. The printed proposition
also asserts that such a `y*` exists; that existence clause is false in general (with `θ ≡ 0` and
`β > r` the budget cost `𝒳(0, ·)` jumps down by `−b(0) > 0` at one multiplier, so some wealth levels
`x > b(0)` admit no `y*`; see the mission description) and is not posed. The proof itself begins
"Suppose that such a y* exists", and p. 14 reads the result as "the solution of the duality
approach, if it exists, can be transformed back into the solution of the primal problem".
Conventions: posed at `t = 0` (the problem of Definition 2.6; `F^S_0` is trivial, so `V`, `𝐋`, `𝒳`
are numbers). The paper's `τ̂_{0,y*}` is replaced by any optimal stopping time of (14) at `y*`
(`IsOptimalStop`), which covers it. Retirement processes are encoded by `F^S`-stopping times
`τ ∈ [0, T1]`, `R = 1{· ≥ τ}`; the atom of `dR` at `τ` is counted in (14) and (17) also when
`τ = 0`. `Z` uses the Itô binder `Iθ`; `𝒵` enters through a continuous positive version `Zv`;
`P̃ = Z_T·P`. The standing hypotheses are: the set-up of §2.1 (`Setting.Standing`); `Iθ` is the Itô integral
`∫_0^· θ dW` (`IsItoIntegral`), which defines `Z` (3); Assumption 2.1; `Zv` is a continuous
positive version of the projected density `𝒵_t = E[Z_T | F^S_t]` (6) (`IsZVersion`); Assumption 2.2
for `U_1` and `U_2`; Assumption 2.3 at `t = 0`; and the integrability of the dual
(`DualIntegrable`, added). The primal class requires `c > 0`, `H_T > 0` and an integrable objective
(added; see `Bclass`). The conclusions use `IsGreatest`/`IsLeast` rather than `sSup`/`inf` on `ℝ`. -/
theorem proposition_2_4 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2) :
    (∀ x : ℝ, b p 0 < x → ∀ ystar : ℝ, 0 < ystar →
      ∀ (τhat : Ω → ℝ≥0) (hτhat : IsRetirementTime p st τhat),
      IsOptimalStop p st Zv U1 U2 ystar τhat hτhat →
      Xcal p st Iθ Zv U1 U2 ystar τhat = ENNReal.ofReal (x - b p 0) →
      ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
        (⟨cstar p Zv U1 ystar, H, τhat⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x ∧
        IsGreatest (J p st U1 U2 '' Bclass p st Iθ U1 U2 x)
          (J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
        V0 p st Iθ U1 U2 x = J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩ ∧
        IsLeast ((fun y => L0 p st Zv U1 U2 y + y * (x - b p 0)) '' Ioi 0)
          (J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
        L0 p st Zv U1 U2 ystar + ystar * (x - b p 0) =
          J p st U1 U2 ⟨cstar p Zv U1 ystar, H, τhat⟩) ∧
    (∀ x : ℝ, 0 < x → ∀ ystar : ℝ, 0 < ystar →
      X12 p st Iθ Zv U1 U2 ystar = ENNReal.ofReal x →
      ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
        (cstar p Zv U1 ystar, H) ∈ B1class p st Iθ U1 U2 x ∧
        IsGreatest (J1 p st U1 U2 '' B1class p st Iθ U1 U2 x)
          (J1 p st U1 U2 (cstar p Zv U1 ystar, H)) ∧
        V1 p st Iθ U1 U2 x = J1 p st U1 U2 (cstar p Zv U1 ystar, H) ∧
        IsLeast ((fun y => L1 p st Zv U1 U2 y + y * x) '' Ioi 0)
          (J1 p st U1 U2 (cstar p Zv U1 ystar, H)) ∧
        L1 p st Zv U1 U2 ystar + ystar * x = J1 p st U1 U2 (cstar p Zv U1 ystar, H)) := by sorry

end RetirePartialInfo.Duality
