-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_fh_of_excess_to_finite_set
-- name    : SennottDP.FiniteHorizon.fh_of_excess_to_finite_set
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:42:45.734756+00:00
-- url     : https://prove2.me/theorems/16dc57be-16c5-4725-9d4a-e5901dafb5f2
-- title:
--   Proposition 3.3.2 — an ATAS sending excess probability to a finite set satisfies FH(α, n)
-- statement:
--   Let $\Delta$ be an MDC with countable state space and terminal cost $F$, and let $0 < \alpha \le 1$. Assume $v_{\alpha,n}(i) < \infty$ for all $i \in S$ and $n \ge 1$. Let $(\Delta_N)$ be an augmentation type approximating sequence, with augmentation distributions $q$, that sends excess probability to a finite set $G \subseteq S$:
--   $$
--   \sum_{j \in G} q_j(i,a,r,N) = 1 .
--   $$
--   Then Assumption FH($\alpha$, $n$) holds for all $n \ge 1$.
--
--   This covers unbounded costs, provided the truncation returns the probability mass leaving $S_N$ to a fixed finite set of states.
--
--   **Formalization Note** The book's "for all $\alpha$" is read as: for every $\alpha \in (0,1]$ at which the hypothesis $v_{\alpha,n} < \infty$ holds (the statement quantifies over $\alpha$ as a whole). The sum over $G$ runs over $G \cap S_N$, where $q$ is defined.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 45, Proposition 3.3.2 (proof pp. 45–48)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition 3.3.2 (Sennott, p. 45). Let `0 < α ≤ 1` and assume `v_{α,n} < ∞` for `n ≥ 1`.
Let `(Δ_N)` be an ATAS, with augmentation distributions `q`, that sends excess probability to a
finite set `G`. Then FH(α, n) holds for all `n ≥ 1`. -/
theorem fh_of_excess_to_finite_set {S Act : Type} [Countable S] (M : MDC S Act)
    (F : S → ℝ≥0) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hfin : ∀ n, 1 ≤ n → ∀ i, M.value F α n i < ⊤)
    (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) (hq : AS.IsATASWith q)
    (G : Finset S) (hG : AS.SendsExcessTo q (G : Set S)) :
    ∀ n, 1 ≤ n → AS.FH F α n := by sorry

end SennottDP.FiniteHorizon
