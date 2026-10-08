-- Prove2me | Theorems.Thm_RiskSensMDP_Discounted_value_iteration
-- name    : RiskSensMDP.Discounted.value_iteration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:34.986371+00:00
-- url     : https://prove2.me/theorems/d670103e-af85-4983-a067-81f614c42015
-- title:
--   Theorem 3.6(b) — finite-horizon discounted value iteration
-- statement:
--   In the bounded positive-cost model under (CC), let $V_n$ be the infimum of expected utility over all measurable history-dependent policies. On the extended state space $\hat E$, the zero-stage value is $U(y)$; for $1\le n\le N$ the next value is obtained from the previous one by the minimum operator:
--
--   $$V_0(x,y,z)=U(y),\qquad V_n(x,y,z)=\inf_{a\in D(x)}\int V_{n-1}(x',y+zc(x,a),z\beta)\,Q(dx'\mid x,a).$$
--
--   Each $V_n$ belongs to $C(\hat E)$ for $0\le n\le N$. The formula computes the original policy infimum by dynamic programming rather than defining it as the recursion.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), p. 11, Theorem 3.6(b)

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_Model

open MeasureTheory ProbabilityTheory Filter

namespace RiskSensMDP.Discounted

/-- Theorem 3.6(b), authors' manuscript p. 11: the value defined by the infimum
over all history policies satisfies the Bellman iteration and lies in `C(Ê)`.
Formalization Note: the base equation `V₀=U` is explicit; the recursion is restricted
to `1 ≤ n ≤ N`. -/
theorem value_iteration {E A : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [StandardBorelSpace A]
    (M : Model E A) (hBounds : HasBounds M) (hCC : HasCC M)
    (N : ℕ) :
    (∀ s ∈ extendedDomain E,
      value M 0 s.1 s.2.1 s.2.2 = M.U s.2.1) ∧
    (∀ n ≤ N, InClass M (fun s => value M n s.1 s.2.1 s.2.2)) ∧
    (∀ n ∈ Finset.Icc 1 N, ∀ s ∈ extendedDomain E,
      value M n s.1 s.2.1 s.2.2 =
        minimumOperator M (fun t => value M (n - 1) t.1 t.2.1 t.2.2) s) := by sorry

end RiskSensMDP.Discounted
