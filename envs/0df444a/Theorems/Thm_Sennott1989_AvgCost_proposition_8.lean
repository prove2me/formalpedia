-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_proposition_8
-- name    : Sennott1989.AvgCost.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:07.349837+00:00
-- url     : https://prove2.me/theorems/2b73ce57-d138-43fc-bdf0-99415f7e2c18
-- title:
--   Proposition 8 — the variable-service-rate queue has an average cost optimal stationary policy if λ^(n+1) < ∞ and λ < max_a aβ, and satisfies (6) if λ < min_a aβ
-- statement:
--   Consider the queueing model with variable service rates of Example 2: in each slot $i$ customers arrive with probability $p_i$; when the system is nonempty the server picks one of finitely many decision variables $a$ and serves at rate $a\beta\in(0,1)$. Assume the cost structure of p. 631: $B(a)>0$, $Q$ a polynomial of degree $n\ge0$ that is nonnegative and increasing on $i\ge0$, $C(0)=Q(0)$ and $C(i,a)=Q(i)+B(a)$ for $i\ge1$. Let $\lambda^{(k)}=\sum_ii^kp_i$ and $\lambda=\lambda^{(1)}$, and assume $\lambda^{(n+1)}<\infty$.
--
--   1. If $\lambda<\max_a(a\beta)$, then there exists an average cost optimal stationary policy: a stationary policy $f$ and a finite constant $g$ with $g=g_f(i)\le g_\theta(i)$ for every policy $\theta$ and state $i$.
--   2. If $\lambda<\min_a(a\beta)$, then the average cost optimality equation holds: there are a constant $g$ and a function $h$, bounded below, with
--   $$g+h(i)=\min_a\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\},\qquad i\ge0,\tag{6}$$
--   where $g$ is the optimal average cost: $g=\lim_{\alpha\uparrow1}(1-\alpha)V_\alpha(i)$ for every $i$, and some stationary policy is average cost optimal with average cost $g$.
--
--   The result shows that serving faster than the mean arrival rate under at least one decision suffices for an optimal stationary policy, with holding costs of any polynomial growth, provided the matching moment of the arrivals is finite.
--
--   **Formalization Note** $\lambda<\max_a(a\beta)$ and $\lambda<\min_a(a\beta)$ are written "for some $a$" and "for every $a$". $\lambda^{(n+1)}<\infty$ is summability of $i^{n+1}p_i$; the second sentence is read under it, as in the paper's proof. In (6), $g$ and $h$ are those of part (i) of the Theorem, so (6) is not satisfied by an arbitrary pair; the sums against $h$ are extended-real.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, p. 631, Proposition 8

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Definitions.Def_Sennott1989_AvgCost_Queue

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §3, Proposition 8, p. 631. Consider the queueing model with variable service
rates of Example 2 under the cost structure of p. 631: arrival law `(p_i)`, service rates
`a β ∈ (0, 1)` for finitely many decision variables `a`, service costs `B(a) > 0`, and a polynomial
`Q` of degree `n ≥ 0`, nonnegative and increasing on `i ≥ 0`, with `C(0) = Q(0)` and
`C(i, a) = Q(i) + B(a)` for `i ≥ 1`. Let `λ^(k) = ∑_i i^k p_i` and `λ = λ^(1)`. Assume
`λ^(n+1) < ∞`.

1. If `λ < max_a (aβ)`, then there exists an average cost optimal stationary policy.
2. If `λ < min_a (aβ)`, then the average cost optimality equation (6) holds: there are a constant
   `g` and a function `h` bounded below with `g + h(i) = min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }`
   for all `i ≥ 0`, where `g` is the optimal average cost (`g = lim_{α↑1} (1 − α) V_α(i)` for every
   `i`, attained by an average cost optimal stationary policy).

**Formalization Note** `λ < max_a (aβ)` is `∃ x, λ < a(x)β` and `λ < min_a (aβ)` is
`∀ x, λ < a(x)β` (equivalent over a finite nonempty set). `λ^(n+1) < ∞` is summability of
`i^{n+1} p_i`; the second sentence is read under it, as the paper's proof does. "Average cost
optimal" is `IsACOptimal` (a finite constant `g = g_f(i) ≤ g_θ(i)` for all policies `θ`). In (6) `g`
and `h` are those of part (i) of the Theorem: `g` is the optimal average cost, not an arbitrary
constant, and `h` is bounded below; the sums are extended-real (`SennottDP.SEN.wsum`). -/
theorem proposition_8 {Act : Type} [Fintype Act] [Nonempty Act] (q : QueueData Act)
    (hmom : Summable fun i : ℕ => (i : ℝ) ^ (q.n + 1) * (q.p i : ℝ)) :
    ((∃ x, q.lam < q.a x * q.β) →
        ∃ (f : StationaryPolicy q.toMDC) (g : ℝ), IsACOptimal q.toMDC f g) ∧
      ((∀ x, q.lam < q.a x * q.β) →
        ∃ (g : ℝ) (h : ℕ → ℝ), IsAbelLimit q.toMDC g ∧
          (∃ f : StationaryPolicy q.toMDC, IsACOptimal q.toMDC f g) ∧
          BddBelow (Set.range h) ∧ ACOE q.toMDC g h) := by sorry

end Sennott1989.AvgCost
