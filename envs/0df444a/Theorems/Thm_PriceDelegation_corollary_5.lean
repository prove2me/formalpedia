-- Prove2me | Theorems.Thm_PriceDelegation_corollary_5
-- name    : PriceDelegation.corollary_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:41.610956+00:00
-- url     : https://prove2.me/theorems/a0dace7e-8a34-4f7d-bdf1-e3b1caf1870b
-- title:
--   Corollary 5 — a static separable contract implements the first-best policy $\varepsilon$-optimally
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, let $1\le K\le N$, and let $\pi^*$ be an optimal first-best policy of Proposition 4 (in the regime of $\rho=K/N$). For every $\varepsilon>0$ there is a static contract $t$ — non-decreasing, $t\ge0$, $t(0)=0$, $E[t(V)]<\infty$ — whose separable contract $T=\{t\}$, $T(Y_1,\dots,Y_N)=\sum_i t(Y_i)$, is $\varepsilon$-optimal,
--   $$
--   E[\mathrm{Rev}(\pi^*)-T]=\mathrm{Rev}(\pi^*)-P(\pi^*,T)\ \ge\ J^{FB-MC}-\varepsilon,
--   $$
--   and such that $(\pi^*,T)$ satisfies (participation-multi), $P(\pi^*,T)-C(\pi^*)\ge0$, and (IC-multi): $\pi^*$ is inventory feasible and maximizes $P(\pi,T)-C(\pi)$ over all inventory-feasible policies $\pi$.
--
--   Even with limited liability, inventory constraints and unobservable learning, the firm can approach its first-best payoff with a contract that pays a fixed function of each sale's revenue.
--
--   Differences from the source:
--   - reading: "Let π* be the optimal first-best policy" → any policy of Proposition 4 in its regime, with the free coordinates arbitrary and $\lambda^{n-l}$ any minimizer of $g$; reason: the optimum is not unique (p.26), and p.30 calls π* "the policy π* from Proposition 4"
--   - encoding: $E[\mathrm{Rev}(\pi^*)-T]$ → $\mathrm{Rev}(\pi^*)-P(\pi^*,T)$; reason: $P(\pi,T)=E[T]$ under $\pi$ (p.30)
--   - generalization: $J^{FB-MC}$ as the value of (6), with $I(\pi)=K$ (p.23) → the supremum over policies with $I(\pi)\le K$, the definition of $J^{FB-MC}$ on p.23 before the "without loss of generality"; reason: the value can only be larger, so a lower bound on the payoff in terms of it is stronger; Proposition 4 shows the two agree
--   - generalization: prices $\theta_i(\cdot)>0$, $\varphi_i>0$ in $\Pi$ (p.21), $\geq0$ in (6) (p.23), with the price $\infty$ allowed (p.9) → every price ranges over $[0,\infty]$; reason: a larger policy set: (IC-multi) quantifies over more deviations and $J^{FB-MC}$ over more policies; the target policies are in both sets, so the statement specializes to the page's
--   - encoding: informed price policies $\theta_i(\cdot)$ (p.21) → $\theta_i$ is measurable; reason: the expectations $E[1\{V\ge\theta_i(V)\}]$ that define $I$, Rev and $P$ exist only for measurable $\theta_i$
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Corollary 5, p.31; proof, p.ec13

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Corollary 5 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of
Sept. 22, 2021), p.31). Let `π*` be an optimal first-best policy of Proposition 4. For every
`ε > 0` there is a static separable contract `T = {t}` (`t` non-decreasing, `t ≥ 0`, `t(0) = 0`,
`E[t(V)] < ∞`) that is `ε`-optimal, `E[Rev(π*) − T] ≥ J^{FB−MC} − ε`, and such that `(π*, T)`
satisfies (participation-multi) and (IC-multi).

**Formalization Note** `E[Rev(π*) − T]` is `Rev(π*) − P(π*, T)` (p.30). (IC-multi) ranges over all
inventory-feasible policies with prices in `[0, ∞]`. -/
theorem corollary_5 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V)
    {π : Policy N} (hπ : IsFirstBestPolicy V ψ N K π) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ → ℝ, IsStaticContract V t ∧
      firstBestValue V ψ N K - ε ≤ Rev V π - pay V π t ∧
      Participates V ψ π t ∧ IsBestResponse V ψ K π t := by sorry

end PriceDelegation
