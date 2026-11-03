-- Prove2me | Theorems.Thm_PricingInvCensored_theorem_1
-- name    : PricingInvCensored.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:10.997598+00:00
-- url     : https://prove2.me/theorems/7787ddee-3670-4553-b3cb-a538ad6fa1a7
-- title:
--   Theorem 1 (corrected: instance-dependent constant; nonnegative demand): Algorithm 3 has regret $O(\sqrt T\ln^2T)$ with probability $1-O(1/T)$
-- statement:
--   There is a universal constant $c_1$ with the following property. Let an instance satisfy Assumption 1 (with clairvoyant solution $(p^*,y^*)$), Assumption 2, and nonnegative demand. Then there is a constant $C$, depending only on the instance, such that for every horizon $T\ge2$ at which the printed algorithm is defined (every epoch budget $N_\zeta$ is at least $1$), every initial stock $x_1\in[0,\bar y]$, and every sequence $(\varepsilon_t)$ of independent noises with law $\mu$ on any probability space, the prices $p_t$ and stock levels $y_t$ set by Algorithm 3 and its sub-routines with
--   $$C_1=2(b+\overline p+h)\sqrt{\ln T},\qquad C_2=\big[16C_2'C_1s^{-2}\kappa^{-1}(1+(b+h)^{-1})\ln T\big]^2,\qquad C_2'=2(\overline p+h)\bar y+6\overline p+b\bar y(K+1),$$
--   satisfy
--   $$\Pr\Big[\sum_{t=1}^T\big[Q(p^*,y^*)-Q(p_t,y_t)\big]>C\sqrt T\,(\ln T)^2\Big]\le\frac{c_1}{T}.$$
--
--   This is the paper's main upper bound for strongly concave $G$: with censored demand and unobservable rewards, trisection on prices driven by the difference estimator nearly matches the $\Omega(\sqrt T)$ lower bound of pure dynamic pricing.
--
--   Differences from the source:
--   - correction: the bound $O\big((S^2\sqrt{C_2}+\kappa^{-1})\sqrt{T\ln^4(\bar y(\overline p-\underline p)T)}+(b+\overline p+h+\overline p\overline d+\bar y\overline d^{-1}+C_1\kappa^{-1})\ln^2((\overline p-\underline p)T)\big)$ with only numerical constants hidden → $C\sqrt T(\ln T)^2$ with $C$ depending on the instance (the rate of Remark 2 and p. 4); reason: the printed bound is false: with $b=h=1$, $[\underline p,\overline p]=[1/4,1]$, $\lambda(p)=3-2p$, $\mu=\mathrm{Uniform}[-1/2,1/2]$, $\bar y=5T$ and $x_1=0$, the first bisection stage sits at $\bar y/2$ and the following drain holds stock above $1.25T$ for at least $0.41T$ periods, so the regret is about $0.5T^2$ with probability $1$, while the printed bound is $O(T^{1.5}(\ln T)^{3.5})$.
--   - correction: demand may be negative ($\varepsilon_t<-\underline d$) → $\mu((-\infty,-\underline d))=0$; reason: with $\mu=\mathrm{Uniform}[-4,4]$ in the same instance (with $\bar y=20$) every hypothesis holds, negative demand pushes the stock above $y^*(p)$ in a positive fraction of periods, and the regret is linear in $T$.
--   - reading: the initial stock is not specified → every $x_1\in[0,\bar y]$; reason: Algorithm 1 drains any such stock, and the bound does not depend on $x_1$.
--   - reading: a target below the on-hand stock → $y_t=\max(\text{target}_t,x_t)$; reason: an admissible policy has $y_t\ge x_t$ and stock cannot be disposed of.
--   - reading: "offer the lowest price $\underline p$ until current inventory level is below $m_\tau$" → drain periods post $\underline p$ and order nothing, count toward $T$ but not toward the budget $n$; reason: footnote * of Algorithm 1 and "prices and inventory levels set at each review period by Algorithm 3 and its sub-routines".
--   - reading: $G(p)=\max_yQ(p,y)$ and $y^*(p)$ (p. 6; pp. 14, 17 write $y\in[0,\bar y]$) → maximum over all real $y$; reason: p. 6 has no range.
--   - reading: line 14 of Algorithm 1, "$m_\tau$ explored the most" → ties go to the latest stage; reason: the line leaves ties open.
--   - reading: $o_t,\delta_t$ in Algorithm 2 use $\hat y$ → they use the realized level, $\delta_t=y_t-o_t$; reason: this is the observed leftover and equals $\hat y-o_t$ whenever $x_t\le\hat y$.
--   - reading: $\hat u$ uses $F_{\hat\nu'}$ (Algorithm 2, p. 16; p. 20 writes $F_{\hat\nu}$) → $F_{\hat\nu'}$; reason: the pseudocode.
--   - reading: "no inventories are left" → $o_t=y_t$; reason: zero leftover.
--   - reading: "while $T$ review periods have not been reached" → the run is cut off after $T$ periods inside any sub-routine; reason: the regret is over $t=1,\dots,T$.
--   - reading: lines 9 and 12 of Algorithm 1 reset $n_{\tau+1}=0$ → also $g_{\tau+1}=0$; reason: line 2 initializes both and $\hat g_\tau=g_\tau/n_\tau$ is a per-stage mean.
--   - encoding: Theorem 1 for every $T$ → $T\ge2$ and, at every epoch, $x_\zeta+\lceil\log_2(x_\zeta\bar y)\rceil>0$ and $N_\zeta\ge1$ for $x_\zeta=C_2/(\beta_\zeta-\alpha_\zeta)^4$; reason: these only exclude horizons where the printed algorithm takes the logarithm of a nonpositive number or divides by $n=0$ ($\ln 1=0$ makes $C_1=C_2=0$ at $T=1$).
--   - encoding: costs $b,h$, the bound $|f_\mu'(u)|\le K$, and $s^2$ → $b\ge0$, $h>0$, $f_\mu$ differentiable at every $u$ of the band, and $s^2$ with $s>0$; reason: the paper's costs are nonnegative and $h>0$ is forced by Assumption 1(3) with compact support; a bound on $f_\mu'(u)$ presupposes the derivative; only $s^2$ enters.
--   - encoding: the clairvoyant solution $\arg\max_{p,y}Q$ → any maximizer $(p^*,y^*)$ of $Q$ over $[\underline p,\overline p]\times\mathbb R$; reason: the regret depends only on the optimal value $Q(p^*,y^*)$.
--   - encoding: "with probability $1-O(T^{-1})$" → the bad event has (outer) probability at most $c_1/T$ with $c_1$ universal; reason: the complement form, with the numerical constant of the $O$.
--   - encoding: periods $t=1,\dots,T$ → periods $0,\dots,T-1$ on a probability space in universe `u`; reason: Lean indexing.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Theorem 1 and Remark 2, p.19; proof pp.ec7–ec9

import Mathlib
import Definitions.Def_PricingInvCensored_Model
import Definitions.Def_PricingInvCensored_Controller
import Definitions.Def_PricingInvCensored_Run

open MeasureTheory ProbabilityTheory Set

namespace PricingInvCensored

universe u

/-- **Theorem 1** (corrected: instance-dependent constant; nonnegative demand), Chen, Wang & Zhou,
SSRN 3750413 (2022-10-19), p.19, with Remark 2, p.19.

There is a universal constant `c₁` such that for every instance satisfying Assumptions 1 and 2
(with clairvoyant solution `(p*, y*)`) and nonnegative demand there is a constant `C` such that for
every horizon `T ≥ 2` at which the printed algorithm is defined, every initial stock
`x₁ ∈ [0, ȳ]`, and every i.i.d. noise sequence `ε_t ∼ µ` on any probability space, the run of
Algorithm 3 with `C₁ = 2(b + p̄ + h)√(ln T)` and `C₂ = [16C′₂C₁s⁻²κ⁻¹(1 + (b + h)⁻¹) ln T]²` has
`Pr[Σ_{t=1}^T [Q(p*, y*) − Q(p_t, y_t)] > C √T (ln T)²] ≤ c₁/T`.

**Formalization Note.** `C` depends only on the instance, `c₁` on nothing. The bad event is
bounded in (outer) measure. The run is `regret` of `Def_PricingInvCensored_Run`: drain periods
count toward `T`, nothing is disposed of, and the controller sees only stocks, its own decisions and
sales. -/
theorem theorem_1 :
    ∃ c1 : ℝ, ∀ (I : Instance) (pStar yStar : ℝ), Assumption1 I pStar yStar → Assumption2 I →
      NonnegDemand I →
      ∃ C : ℝ, ∀ T : ℕ, 2 ≤ T → BudgetsDefined I T →
        ∀ x1 ∈ Icc 0 I.ybar, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ),
          ChenChaoShiSALA.Regret.NoiseSequence P I.market ε →
          P {ω | C * Real.sqrt T * Real.log T ^ 2 < regret I (params I T) pStar yStar x1 ε T ω} ≤
            ENNReal.ofReal (c1 / T) := by sorry

end PricingInvCensored
