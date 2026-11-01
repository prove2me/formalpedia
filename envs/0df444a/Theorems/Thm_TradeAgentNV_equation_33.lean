-- Prove2me | Theorems.Thm_TradeAgentNV_equation_33
-- name    : TradeAgentNV.equation_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:10.185771+00:00
-- url     : https://prove2.me/theorems/321de62d-154c-4d8b-ad09-9eb50b5f2c5b
-- title:
--   Displays (32)–(33): the first-order condition has a unique root $b^o\ge0$
-- statement:
--   **The model.** On a probability space $(\Omega,\mathcal F,P)$ the seller's ask price $Z$ and the yield fraction $U$ are independent real random variables. The win probability is $w(b)=P(Z\le b)$, with $P(Z\le0)=0$; $w$ has a derivative $w'(b)>0$ (within $[0,\infty)$) at every $b\ge0$, so the support of $Z$ is $\Omega=[0,\infty)$. The yield satisfies $0\le U\le1$ almost surely and $E[U]>0$. The parameters $D,r,t,h,\pi$ are positive with $r-t+\pi>0$, and the lot size is $q>0$. The expected profit at bid $b$ is
--   $$
--   E[V^y(b)]=E\Big[\mathbf 1\{Z\le b\}\big((r-t)\min(qU,D)-bq-h(qU-D)^+-\pi(D-qU)^+\big)-\mathbf 1\{Z>b\}\,\pi D\Big],
--   $$
--   $\rho=r-t+h+\pi$, and $R=\rho E[\min(qU,D)]-hqE[U]$ is the expected benefit of bidding (7).
--
--   Assume $R>0$ and Assumption 1 ($b\mapsto b+w(b)/w'(b)$ strictly increasing on $[0,\infty)$). Then there is exactly one $b^o\ge0$ with
--   $$
--   b^o+\frac{w(b^o)}{w'(b^o)}=\frac Rq .
--   $$
--   By (31) this is the unique zero of the derivative of the expected profit in $\Omega$.
--
--   Differences from the source:
--   - reading: display (3) charges $h$ on $(D-qU)^+$ and $\pi$ on $(qU-D)^+$ → $h$ on the excess supply $(qU-D)^+$ and $\pi$ on the unmet demand $(D-qU)^+$; reason: p.8 defines $h$ as the excess-supply cost and $\pi$ as the lost-sales cost, and only this assignment gives display (4)
--   - encoding: the bid outcome ($Z\le b$) and the yield $U$ as two separate uncertainties, $Q^y(b)=qU$ w.p. $w(b)$ (2) → $Z$ and $U$ are random variables on one probability space and are independent; reason: (2) multiplies the win probability by the yield distribution, i.e. the yield is independent of the bid outcome; same instances
--   - encoding: $Z$ is a nonnegative, continuous random variable → $P(Z\le0)=0$; reason: for a nonnegative continuous $Z$, $P(Z\le0)=P(Z=0)=0$; conversely with the derivative hypothesis $w$ is continuous and vanishes on $(-\infty,0]$; the proof uses $w(0)=0$
--   - reading: $w$ is differentiable with density $w'=dw/db$ and $\Omega=\{b:w'(b)>0\}=[0,\infty)$ → $w$ has derivative $w'(b)$ within $[0,\infty)$ at every $b\ge0$, and $w'(b)>0$ for $b\ge0$; reason: a two-sided derivative at $0$ is impossible when $w=0$ on $(-\infty,0]$ and $w'(0)>0$; the paper uses the derivative only on $\Omega=[0,\infty)$
--   - encoding: the seller has $q$ units ($D/q$ is used throughout) → $q>0$; reason: implicit in the paper; $D/q$ is undefined at $q=0$
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, proof of Theorem 1, displays (32)–(33), p.29

import Mathlib
import Definitions.Def_TradeAgentNV_winProb
import Definitions.Def_TradeAgentNV_expProfit
import Definitions.Def_TradeAgentNV_expBenefit
import Definitions.Def_TradeAgentNV_Assumption1

open MeasureTheory ProbabilityTheory

namespace TradeAgentNV

/-- **Displays (32)–(33)** (proof of Theorem 1, p.29) of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023): if the
expected benefit of bidding `R = ρE[min(qU, D)] − hqE[U]` is positive and `Z` satisfies
Assumption 1, the first-order condition `dE[Vʸ(b)]/db = 0`, i.e. `b + w(b)/w′(b) = R/q`, has a
unique solution `bᵒ` in `Ω = [0, ∞)`.

**Formalization Note.** The model: on a probability space `(Ω, P)` the ask price `Z` and the
yield fraction `U` are independent random variables (the yield is exogenous to the bid, (2));
`P(Z ≤ 0) = 0` encodes "`Z` nonnegative and continuous" (the proof uses `w(0) = 0`); `w'` is the
density, a derivative of `w` within `Ω = [0, ∞)` (a two-sided derivative at `0` is impossible
when `w = 0` on `(−∞, 0]` and `w'(0) > 0`), positive on `[0, ∞)` (`Ω = {b : w'(b) > 0} = [0, ∞)`,
p.9); `0 ≤ U ≤ 1` a.s. and `E[U] > 0` (p.9); `D, r, t, h, π > 0`, `r − t + π > 0` (p.8) and lot
size `q > 0` (implicit: `D/q` is used throughout). -/
theorem equation_33
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z U : Ω → ℝ) (hZ : Measurable Z) (hU : Measurable U) (hZU : IndepFun Z U P)
    (hZ0 : P.real {ω | Z ω ≤ 0} = 0)
    (w' : ℝ → ℝ)
    (hw : ∀ b, 0 ≤ b → HasDerivWithinAt (winProb P Z) (w' b) (Set.Ici 0) b)
    (hw'pos : ∀ b, 0 ≤ b → 0 < w' b)
    (hU01 : ∀ᵐ ω ∂P, U ω ∈ Set.Icc (0 : ℝ) 1) (hEU : 0 < ∫ ω, U ω ∂P)
    (r t h π D q : ℝ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h) (hπ : 0 < π) (hD : 0 < D)
    (hq : 0 < q) (hrtπ : 0 < r - t + π)
    (hR : 0 < expBenefit P U r t h π D q) (hA : Assumption1 (winProb P Z) w') :
    ∃! bo, 0 ≤ bo ∧ bo + winProb P Z bo / w' bo = expBenefit P U r t h π D q / q := by sorry

end TradeAgentNV
