-- Prove2me | Theorems.Thm_ServiceParts_UnitDecomp_theorem5_base_stock_optimal
-- name    : ServiceParts.UnitDecomp.theorem5_base_stock_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:01:45.786492+00:00
-- url     : https://prove2.me/theorems/47afc65a-17d3-49af-a638-90f924e2d9c1
-- title:
--   Theorem 5 — a state-dependent base-stock policy with level $y^*(n,s_n)-1$ is optimal on a finite horizon
-- statement:
--   Consider the single-location system $\mathcal S$ over a horizon of $N$ periods, with an exogenous finite-state Markov chain $s_n$ governing demand, lead time $m-1$ ($m\ge1$), holding cost $h$, backorder cost $b$ with $0<h<b$, and discount factor $\alpha\in(0,1]$. Let $y^*(n,s)$ be the critical distance of the single-unit single-customer subsystem, and call a policy for $\mathcal S$ **base-stock with levels $y^*-1$** if in every period $1\le n\le N$, in every Markov state $s$ with $y^*(n,s)<\infty$ and every configuration, it releases the lowest-indexed units at the supplier in the number needed to raise the inventory position to
--   $$y^*(n,s) - 1,$$
--   and releases nothing if the inventory position is already at least that level. Then
--
--   1. a base-stock policy with levels $y^*-1$ exists (it orders a finite quantity in every period), and
--   2. every base-stock policy with levels $y^*-1$ is optimal: from every Markov state $s$ and every starting configuration $x_1$, its expected discounted cost over periods $1,\dots,N$ equals the optimal cost $V^{\mathcal S}_1(s,x_1)$ over all policies.
--
--   That is, a state-dependent order-up-to (base-stock) policy is optimal for the whole system on a finite horizon, and its levels are read off the single-unit problem.
--
--   **Formalization Note** In a period where $y^*(n,s)=\infty$ (releasing is optimal for every customer distance, which happens in the last $m-1$ periods when an order cannot arrive before the horizon ends), the book's level $\infty$ is not an order quantity; the statement leaves the policy free there, and every choice is then optimal. The book's "the optimal policy" is read as "an optimal policy": ties make other policies optimal as well. Optimality is against all policies for $\mathcal S$, not only monotone or base-stock ones.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 29, Theorem 5

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem
import Definitions.Def_ServiceParts_UnitDecomp_System

namespace ServiceParts.UnitDecomp

theorem theorem5_base_stock_optimal {σ : Type} [Fintype σ] (M : Model σ) (N : ℕ) :
    (∃ π : SPolicy σ, ∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
      M.criticalDistance N n s ≠ ⊤ →
        π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x) ∧
    ∀ π : SPolicy σ,
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SysState),
        M.criticalDistance N n s ≠ ⊤ →
          π.act n s x = M.baseStockRelease (((M.criticalDistance N n s).toNat : ℤ) - 1) x) →
      ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
        M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀) := by sorry

end ServiceParts.UnitDecomp
