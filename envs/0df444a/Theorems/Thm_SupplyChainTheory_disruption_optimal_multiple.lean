-- Prove2me | Theorems.Thm_SupplyChainTheory_disruption_optimal_multiple
-- name    : SupplyChainTheory.disruption_optimal_multiple
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:48:30.565757+00:00
-- url     : https://prove2.me/theorems/2776eae9-bc1c-4fcd-bee9-8a363e66ad95
-- title:
--   Lemma 9.4: the optimal base-stock level is an integer multiple of $d$
-- statement:
--   **Lemma 9.4.** In the infinite-horizon newsvendor problem with deterministic demand $d > 0$ and
--   supply disruptions ($0 < \alpha, \beta \le 1$, $h, p > 0$), the expected cost per period
--   $g(S) = \sum_n \pi_n \hat g(S, n)$ has a minimizer that is an integer multiple of $d$, and its
--   least minimizer is such a multiple.
--
--   The book's sketch: $g$ is piecewise linear in $S$ with breakpoints at the multiples of $d$, so
--   the minimum of the (convex) function is attained at a breakpoint. This reduces the choice of the
--   base-stock level to a discrete search, which Theorem 9.5 then resolves in closed form.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 363, Sect. 9.2.2.4, Lemma 9.4 and its proof sketch ('g is a piecewise-linear function of S, with breakpoints at multiples of d')

import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_optimal_multiple (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) :
    ∃ k : ℕ, IsMinOn (meanCost α β h p d) Set.univ (k * d)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → k * d ≤ S := by sorry

end SupplyChainTheory
