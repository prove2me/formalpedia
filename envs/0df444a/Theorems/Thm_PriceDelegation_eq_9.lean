-- Prove2me | Theorems.Thm_PriceDelegation_eq_9
-- name    : PriceDelegation.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:29.656534+00:00
-- url     : https://prove2.me/theorems/f2b91c90-c945-480d-8cc1-bb26ea889923
-- title:
--   Eq. (9) — the Lagrangian dual $J_\lambda$ in closed form, and weak duality
-- statement:
--   Let $N$ customers share $K$ units, and let $\lambda\ge0$. Over all policies $\pi$ (learning probabilities $q_i\in[0,1]$, measurable informed price policies, uninformed prices in $[0,\infty]$), the Lagrangian objective of (7),
--   $$\sum_{i=1}^N q_i\big(E[(\theta_i(V)-\lambda)1\{V\ge\theta_i(V)\}]-\psi\big)+(1-q_i)(\varphi_i-\lambda)\bar F(\varphi_i)+K\lambda,$$
--   attains its maximum, and the maximum equals
--   $$
--   J_\lambda=N\cdot\max\Big\{E[(V-\lambda)^+]-\psi,\ \max_{\varphi>0}(\varphi-\lambda)\bar F(\varphi)\Big\}+K\lambda.\qquad(9)
--   $$
--   Moreover every inventory-feasible policy ($I(\pi)\le K$) satisfies $\mathrm{Rev}(\pi)-C(\pi)\le J_\lambda$.
--
--   The closed form turns the dual problem $\min_{\lambda\ge0}J_\lambda$ into a one-dimensional convex problem, and the bound is the weak duality used to certify the optimality of the first-best policies.
--
--   Differences from the source:
--   - generalization: prices $\theta_i(\cdot)>0$, $\varphi_i>0$ in $\Pi$ (p.21), $\geq0$ in (6) (p.23), with the price $\infty$ allowed (p.9) → every price ranges over $[0,\infty]$; reason: a larger policy set: (IC-multi) quantifies over more deviations and $J^{FB-MC}$ over more policies; the target policies are in both sets, so the statement specializes to the page's
--   - encoding: informed price policies $\theta_i(\cdot)$ (p.21) → $\theta_i$ is measurable; reason: the expectations $E[1\{V\ge\theta_i(V)\}]$ that define $I$, Rev and $P$ exist only for measurable $\theta_i$
--   - generalization: the standing assumptions $\psi>0$, Assumptions 1–2 and $1\le K\le N$ of the paper → not assumed; reason: the statement holds without them; the paper's case is the special case where they hold
--   - reading: E[V] < ∞ is not stated → the valuation law has $\int_0^\infty v f(v)\,dv<\infty$; reason: $J^{FB}=E[V]-\psi$ and Assumption 1 compare finite numbers (p.11), and every maximum of §4.3 needs $\varphi\bar F(\varphi)\to0$
--   - encoding: a continuous random variable with density $f$ and support $(0,\infty)$ (p.8) → a measurable density vanishing on $(-\infty,0]$ with positive mass on every interval $[a,b]\subseteq[0,\infty)$, $a<b$; reason: this is what support $(0,\infty)$ means for the law; no condition on $f$ beyond a density is added
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), (7), (8), (9), pp.24–25

import Mathlib
import Definitions.Def_PriceDelegation_Valuation
import Definitions.Def_PriceDelegation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace PriceDelegation

/-- (9) and weak duality (Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055
(version of Sept. 22, 2021), pp.24–25). For every multiplier `λ ≥ 0`, the value of the Lagrangian
relaxation (7) over the policy set `Π` is attained and equals
`J_λ = N · max{E[(V − λ)⁺] − ψ, max_{φ>0} (φ − λ) F̄(φ)} + K · λ` (9), and `J_λ` bounds the
objective `Rev(π) − C(π)` of every inventory-feasible policy (p.24: "`J^{FB−MC} ≤ J_λ^{FB−MC}`").

**Formalization Note** Prices range over `[0, ∞]`. -/
theorem eq_9 (V : Valuation) (ψ : ℝ) (N K : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    IsGreatest {x | ∃ π : Policy N, InPi π ∧ x = lagObj V ψ K lam π} (Jdual V ψ N K lam) ∧
      ∀ π : Policy N, Feasible V K π → Rev V π - cost ψ π ≤ Jdual V ψ N K lam := by sorry

end PriceDelegation
