-- Prove2me | Theorems.Thm_ServiceParts_UnitDecomp_theorem4_decomposition
-- name    : ServiceParts.UnitDecomp.theorem4_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:48:42.521622+00:00
-- url     : https://prove2.me/theorems/8927cc61-bd53-4f19-8e89-6d1d263cf8ab
-- title:
--   Theorem 4 — the optimal cost of $\mathcal S$ is the sum of the optimal subsystem costs, and independent optimal control of the subsystems is optimal
-- statement:
--   Consider the system $\mathcal S$ and its single-unit single-customer subsystems $\mathcal S_w$ over a horizon of $N$ periods ($0<h<b$, $\alpha\in(0,1]$). For a starting configuration $x_1$ in period 1 write $(z_{w1}, y_{w1})$ for the location of unit $w$ and the distance of customer $w$ in $x_1$.
--
--   1. For every Markov state $s$ and every starting configuration $x_1$,
--   $$V^{\mathcal S}_1(s,x_1) = \sum_{w\ge 0} V_1\big(s,(z_{w1},y_{w1})\big),$$
--   where $V^{\mathcal S}_1$ is the optimal expected discounted cost of $\mathcal S$ in periods $1,\dots,N$ and $V_1$ that of a subsystem.
--   2. Let $\rho$ be a subsystem policy that is optimal in every period: $C^\rho_n(s,x) = V_n(s,x)$ for all $1\le n\le N$, all $s$ and all configurations $x=(z,y)$. Let $\pi$ be a policy for $\mathcal S$ that, in every period $n$ and configuration, releases exactly the units $j$ at the supplier for which $\rho$ releases in the subsystem state $(s_n, z_{jn}, y_{jn})$, whenever this set is finite. Then $\pi$ is optimal for $\mathcal S$:
--   $$C^\pi_1(s,x_1) = V^{\mathcal S}_1(s,x_1)$$
--   for every $s$ and every starting configuration $x_1$.
--
--   This is the decomposition of the single-location system into countably many independent unit–customer problems, which reduces the structure of an optimal policy for $\mathcal S$ to that of a two-action problem.
--
--   **Formalization Note** The sum over subsystems is taken in $[0,\infty]$. The book's "any starting state $x_1$" is read as the starting configurations built on pp. 23–24. In the second part, "managed independently and optimally using the state vector $x^w_n$ in every period $n$" is a subsystem policy depending on $(n, s_n, z_{wn}, y_{wn})$ that is optimal from every period and state; the policy for $\mathcal S$ is unconstrained in configurations where $\rho$ would release infinitely many units, since an order quantity is a nonnegative integer.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 27, Theorem 4

import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem
import Definitions.Def_ServiceParts_UnitDecomp_System

namespace ServiceParts.UnitDecomp

theorem theorem4_decomposition {σ : Type} [Fintype σ] (M : Model σ) (N : ℕ) :
    (∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
      M.sysOpt N 1 s (M.initState a v₀) =
        ∑' w : ℕ, M.subOpt N 1 s ((M.initState a v₀).loc w, (M.initState a v₀).dist w)) ∧
    ∀ ρ : SubPolicy σ,
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ (s : σ) (x : SubState),
        M.subCost N ρ n s x = M.subOpt N n s x) →
      ∀ π : SPolicy σ,
        (∀ (n : ℕ) (s : σ) (x : SysState),
          {j | x.loc j = M.m + 1 ∧ ρ n s (x.loc j, x.dist j) = Decision.release}.Finite →
            π.act n s x = {j | x.loc j = M.m + 1 ∧ ρ n s (x.loc j, x.dist j) = Decision.release}) →
        ∀ (s : σ) (a : ℕ → ℕ) (v₀ : ℕ),
          M.sysCost N π 1 s (M.initState a v₀) = M.sysOpt N 1 s (M.initState a v₀) := by sorry

end ServiceParts.UnitDecomp
