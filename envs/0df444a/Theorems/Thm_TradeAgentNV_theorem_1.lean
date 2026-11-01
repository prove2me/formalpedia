-- Prove2me | Theorems.Thm_TradeAgentNV_theorem_1
-- name    : TradeAgentNV.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:12.766505+00:00
-- url     : https://prove2.me/theorems/3dd99a19-717b-4f28-b262-5de0e01ecab6
-- title:
--   Theorem 1: the trade agent's unique optimal bid
-- statement:
--   **The model.** On a probability space $(\Omega,\mathcal F,P)$ the seller's ask price $Z$ and the yield fraction $U$ are independent real random variables. The win probability is $w(b)=P(Z\le b)$, with $P(Z\le0)=0$; $w$ has a derivative $w'(b)>0$ (within $[0,\infty)$) at every $b\ge0$, so the support of $Z$ is $\Omega=[0,\infty)$. The yield satisfies $0\le U\le1$ almost surely and $E[U]>0$. The parameters $D,r,t,h,\pi$ are positive with $r-t+\pi>0$, and the lot size is $q>0$. The expected profit at bid $b$ is
--   $$
--   E[V^y(b)]=E\Big[\mathbf 1\{Z\le b\}\big((r-t)\min(qU,D)-bq-h(qU-D)^+-\pi(D-qU)^+\big)-\mathbf 1\{Z>b\}\,\pi D\Big],
--   $$
--   $\rho=r-t+h+\pi$, and $R=\rho E[\min(qU,D)]-hqE[U]$ is the expected benefit of bidding (7).
--
--   Write $\kappa=\rho E[\min(U,D/q)]-hE[U]$ $(=R/q)$ and $\theta=E[\min(U,D/q)]/E[U]$ for the expected sales-to-supply ratio. Then:
--   1. If $\theta\le h/\rho$, then $E[V^y(b)]$ is strictly decreasing in $b$ over $[0,\infty)$, and $b^*=0$ is the unique optimal bid.
--   2. If $\theta>h/\rho$ and $Z$ satisfies Assumption 1, then $E[V^y(b)]$ is unimodal on $[0,\infty)$ and its unique optimal bid $b^*$ is positive.
--   3. If $Z$ satisfies Assumption 1, the unique optimal bid in $[0,\infty)$ is
--   $$
--   b^*=\begin{cases}0 & \text{if } \theta\le h/\rho,\\ b^o & \text{otherwise,}\end{cases}
--   $$
--   where $b^o$ is the unique solution in $[0,\infty)$ of
--   $$
--   b^o+\frac{w(b^o)}{w'(b^o)}=\rho E\Big[\min\Big(U,\frac Dq\Big)\Big]-hE[U],
--   $$
--   and $0<b^o<\rho E[\min(U,D/q)]-hE[U]$.
--   4. If $Z$ satisfies Assumption 1 and $D/q>h/\rho$, then $b^*=b^o>0$.
--
--   Bidding pays exactly when the expected sales-to-supply ratio exceeds the newsvendor-type threshold $h/\rho$, whatever the ask-price distribution; nothing is assumed on the law of the yield beyond $0\le U\le1$ and $E[U]>0$.
--
--   **Formalization Note** Assumption 1 is the predicate `Assumption1 w w'`; "unimodal" is `Unimodal` (strictly increasing on $[0,m]$, strictly decreasing on $[m,\infty)$ for some $m\ge0$); the optimal-bid set is the argmax over $[0,\infty)$.
--
--   Differences from the source:
--   - reading: display (3) charges $h$ on $(D-qU)^+$ and $\pi$ on $(qU-D)^+$ → $h$ on the excess supply $(qU-D)^+$ and $\pi$ on the unmet demand $(D-qU)^+$; reason: p.8 defines $h$ as the excess-supply cost and $\pi$ as the lost-sales cost, and only this assignment gives display (4)
--   - encoding: the bid outcome ($Z\le b$) and the yield $U$ as two separate uncertainties, $Q^y(b)=qU$ w.p. $w(b)$ (2) → $Z$ and $U$ are random variables on one probability space and are independent; reason: (2) multiplies the win probability by the yield distribution, i.e. the yield is independent of the bid outcome; same instances
--   - encoding: $Z$ is a nonnegative, continuous random variable → $P(Z\le0)=0$; reason: for a nonnegative continuous $Z$, $P(Z\le0)=P(Z=0)=0$; conversely with the derivative hypothesis $w$ is continuous and vanishes on $(-\infty,0]$; the proof uses $w(0)=0$
--   - reading: $w$ is differentiable with density $w'=dw/db$ and $\Omega=\{b:w'(b)>0\}=[0,\infty)$ → $w$ has derivative $w'(b)$ within $[0,\infty)$ at every $b\ge0$, and $w'(b)>0$ for $b\ge0$; reason: a two-sided derivative at $0$ is impossible when $w=0$ on $(-\infty,0]$ and $w'(0)>0$; the paper uses the derivative only on $\Omega=[0,\infty)$
--   - encoding: the seller has $q$ units ($D/q$ is used throughout) → $q>0$; reason: implicit in the paper; $D/q$ is undefined at $q=0$
--   - reading: $E[V^y(b)]$ is decreasing in $b$ → strictly decreasing on $[0,\infty)$; reason: the stronger reading; the proof (p.28) gives $E[V^y(0)]>E[V^y(b)]$ for $b>0$ and uniqueness of $b^*=0$
--   - reading: $E[V^y(b)]$ is unimodal → strictly increasing on $[0,m]$ and strictly decreasing on $[m,\infty)$ for some $m\ge0$; reason: the stronger reading, which the proof establishes (p.29)
--   - reading: $b^o$ solves (6) → $b^o$ solves (6) and is its only solution in $[0,\infty)$; reason: the proof calls $b^o$ the unique solution (p.29); the stronger reading
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, Theorem 1, pp.10–11

import Mathlib
import Definitions.Def_TradeAgentNV_winProb
import Definitions.Def_TradeAgentNV_expProfit
import Definitions.Def_TradeAgentNV_expBenefit
import Definitions.Def_TradeAgentNV_salesSupplyRatio
import Definitions.Def_TradeAgentNV_Assumption1
import Definitions.Def_TradeAgentNV_optimalBids
import Definitions.Def_TradeAgentNV_Unimodal

open MeasureTheory ProbabilityTheory

namespace TradeAgentNV

/-- **Theorem 1** (pp.10–11) of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023). Write `w(b) = P(Z ≤ b)`,
`V(b) = E[Vʸ(b)]` for the expected profit, `ρ = r − t + h + π` and
`κ = ρE[min(U, D/q)] − hE[U]`.
(i) If `E[min(U, D/q)]/E[U] ≤ h/ρ`, then `V` is (strictly) decreasing over `Ω = [0, ∞)` and
`b* = 0` is the unique optimal bid.
(ii) If `E[min(U, D/q)]/E[U] > h/ρ` and `Z` satisfies Assumption 1, then `V` is unimodal and
the unique optimal bid `b*` is positive.
(iii) If `Z` satisfies Assumption 1, the unique optimal bid is `b* = 0` when
`E[min(U, D/q)]/E[U] ≤ h/ρ`, and otherwise `b* = bᵒ`, where `bᵒ` is the unique solution in
`Ω` of `bᵒ + w(bᵒ)/w′(bᵒ) = κ` (6), and `0 < bᵒ < κ`.
(iv) If `Z` satisfies Assumption 1 and `D/q > h/ρ`, then `b* = bᵒ > 0`.

**Formalization Note.** The model: on a probability space `(Ω, P)` the ask price `Z` and the
yield fraction `U` are independent random variables (the yield is exogenous to the bid, (2));
`P(Z ≤ 0) = 0` encodes "`Z` nonnegative and continuous" (the proof uses `w(0) = 0`); `w'` is the
density, a derivative of `w` within `Ω = [0, ∞)` (a two-sided derivative at `0` is impossible
when `w = 0` on `(−∞, 0]` and `w'(0) > 0`), positive on `[0, ∞)` (`Ω = {b : w'(b) > 0} = [0, ∞)`,
p.9); `0 ≤ U ≤ 1` a.s. and `E[U] > 0` (p.9); `D, r, t, h, π > 0`, `r − t + π > 0` (p.8) and lot
size `q > 0` (implicit: `D/q` is used throughout). Display (3) swaps `h` and `π`; the profit follows p.8 and display (4) (see
`wonProfit`). "Decreasing" is read as strictly decreasing and "unimodal" as strictly increasing
then strictly decreasing (`Unimodal`). -/
theorem theorem_1
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z U : Ω → ℝ) (hZ : Measurable Z) (hU : Measurable U) (hZU : IndepFun Z U P)
    (hZ0 : P.real {ω | Z ω ≤ 0} = 0)
    (w' : ℝ → ℝ)
    (hw : ∀ b, 0 ≤ b → HasDerivWithinAt (winProb P Z) (w' b) (Set.Ici 0) b)
    (hw'pos : ∀ b, 0 ≤ b → 0 < w' b)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π) :
    let w := winProb P Z
    let V := fun b => expProfit P Z U r t h π D q b
    let ρ := rho r t h π
    let κ := ρ * ∫ ω, min (U ω) (D / q) ∂P - h * ∫ ω, U ω ∂P
    -- (i)
    (salesSupplyRatio P U D q ≤ h / ρ →
        StrictAntiOn V (Set.Ici 0) ∧ optimalBids V = {0}) ∧
    -- (ii)
    (h / ρ < salesSupplyRatio P U D q → Assumption1 w w' →
        Unimodal V ∧ ∃ b, 0 < b ∧ optimalBids V = {b}) ∧
    -- (iii)
    (Assumption1 w w' →
        (salesSupplyRatio P U D q ≤ h / ρ → optimalBids V = {0}) ∧
        (h / ρ < salesSupplyRatio P U D q →
          ∃ bo, bo + w bo / w' bo = κ ∧ (∀ b, 0 ≤ b → b + w b / w' b = κ → b = bo) ∧
            0 < bo ∧ bo < κ ∧ optimalBids V = {bo})) ∧
    -- (iv)
    (Assumption1 w w' → h / ρ < D / q →
        ∃ bo, 0 < bo ∧ bo + w bo / w' bo = κ ∧ optimalBids V = {bo}) := by sorry

end TradeAgentNV
