-- Prove2me | Theorems.Thm_PriceDelegation_proposition_4
-- name    : PriceDelegation.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:49.970102+00:00
-- url     : https://prove2.me/theorems/bdcbdf0b-58c1-47d5-9e3d-97dc1cadbc45
-- title:
--   Proposition 4 — the policies $\pi^{n-l}$, $\pi^{p-l}$, $\pi^{f-l}$ solve the first-best problem (6) in their regimes
-- statement:
--   Let $\psi>0$, let the valuation satisfy Assumptions 1 and 2, and let $1\le K\le N$, $\rho=K/N$. Let $\lambda^{p-l}$ be the zero of $\Delta$ and $\varphi^{p-l}=\varphi^*(\lambda^{p-l})$. The first-best policy is
--   $$
--   \pi^*=\begin{cases}\pi^{n-l},&\rho\le\bar F(\varphi^{p-l}),\\ \pi^{p-l},&\bar F(\varphi^{p-l})\le\rho\le\bar F(\lambda^{p-l}),\\ \pi^{f-l},&\rho\ge\bar F(\lambda^{p-l}),\end{cases}
--   $$
--   with the three policies as defined in the model. Precisely:
--
--   1. such a policy $\pi^*$ exists for every $1\le K\le N$;
--   2. every such $\pi^*$ is inventory feasible and consumes exactly $K$ units, $I(\pi^*)=K$;
--   3. $\mathrm{Rev}(\pi^*)-C(\pi^*)$ is the largest value of $\mathrm{Rev}(\pi)-C(\pi)$ over inventory-feasible policies, hence equals $J^{FB-MC}$.
--
--   So $\pi^*$ is an optimal solution of (6), and the Lagrangian relaxation is tight (Corollary 4).
--
--   Differences from the source:
--   - reading: "the optimal solution to (6) is" $\pi^{n-l}$, $\pi^{p-l}$ or $\pi^{f-l}$ → each such policy is an optimal solution, with the coordinates the paper calls arbitrary left free and $\lambda^{n-l}$ any minimizer of $g$; reason: the optimum is not unique ($\varphi_i$ is free when $q_i=1$, $\theta_i$ when $q_i=0$, p.26), and the paper says "one of the three policies … is always optimal" (p.26)
--   - generalization: $J^{FB-MC}$ as the value of (6), with $I(\pi)=K$ (p.23) → the supremum over policies with $I(\pi)\le K$, the definition of $J^{FB-MC}$ on p.23 before the "without loss of generality"; reason: the value can only be larger, so a lower bound on the payoff in terms of it is stronger; Proposition 4 shows the two agree
--   - generalization: prices $\theta_i(\cdot)>0$, $\varphi_i>0$ in $\Pi$ (p.21), $\geq0$ in (6) (p.23), with the price $\infty$ allowed (p.9) → every price ranges over $[0,\infty]$; reason: a larger policy set: (IC-multi) quantifies over more deviations and $J^{FB-MC}$ over more policies; the target policies are in both sets, so the statement specializes to the page's
--   - encoding: informed price policies $\theta_i(\cdot)$ (p.21) → $\theta_i$ is measurable; reason: the expectations $E[1\{V\ge\theta_i(V)\}]$ that define $I$, Rev and $P$ exist only for measurable $\theta_i$
--   - reading: $K$ units, $K\le N$ (p.20) → $1\le K\le N$; reason: the paper speaks of multiple units and $\rho=0$ has no $\lambda^{f-l}$; $N=K=1$ is allowed
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), Proposition 4, p.27; the policies, p.26; proof, p.ec9

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- Proposition 4 (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version
of Sept. 22, 2021), p.27): in each regime of `ρ = K/N`, the corresponding policy `π^{n-l}`,
`π^{p-l}` or `π^{f-l}` (`IsFirstBestPolicy`) is an optimal solution of the first-best problem (6):
it is inventory feasible, consumes exactly `K` units, and attains the largest `Rev(π) − C(π)`
among inventory-feasible policies, so it attains `J^{FB−MC}`. Such a policy exists for every
`1 ≤ K ≤ N` (the regimes cover `ρ ∈ (0, 1]`, and `η` exists, p.27). -/
theorem proposition_4 (V : Valuation) {ψ : ℝ} (hψ : 0 < ψ) {N K : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N)
    (hA1 : Assumption1 V ψ) (hA2 : Assumption2 V) :
    (∃ π : Policy N, IsFirstBestPolicy V ψ N K π) ∧
      ∀ π : Policy N, IsFirstBestPolicy V ψ N K π →
        Feasible V K π ∧ invUse V π = K ∧
          IsGreatest {x | ∃ π' : Policy N, Feasible V K π' ∧ x = Rev V π' - cost ψ π'}
            (Rev V π - cost ψ π) ∧
          firstBestValue V ψ N K = Rev V π - cost ψ π := by sorry

end PriceDelegation
