-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_theorem_3_1
-- name    : StochSchedPrec.InForest.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:52.950405+00:00
-- url     : https://prove2.me/theorems/cbeb61f0-1c39-469e-9113-52a6ae5ac82e
-- title:
--   Theorem 3.1, p. 797 — the load inequalities Σ_{j∈W} E[P_j] E[C^Π_j] ≥ f(W) for nonanticipatory policies
-- statement:
--   Consider $m\ge 1$ identical machines, acyclic precedence constraints $A$ on a finite job set $V$, no release dates, and independent nonnegative processing times $P_j$ with $\mathrm{CV}[P_j]\le\sqrt\Delta$ for all $j$ and some $\Delta\ge0$. Let $f$ be the set function (3.1) built from $\mu_j=\mathrm E[P_j]$. Then for every feasible nonanticipatory scheduling policy $\Pi$ (with integrable completion times) and every $W\subseteq V$, the load inequality
--   $$\sum_{j\in W}\mathrm E[P_j]\,\mathrm E[C^\Pi_j(P)]\ \ge\ f(W) \tag{3.2}$$
--   holds.
--
--   The load inequalities, due to Möhring, Schulz and Uetz, are what makes the LP of §3 a relaxation of the stochastic problem.
--
--   **Formalization Note** The CV bound includes $\mathrm E[P_j^2]<\infty$ and $\mathrm E[P_j]>0$; the comparator's completion times are assumed integrable (a policy with infinite expected completion time makes (3.2) trivial on the page but would read as $0$ in Lean).
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, Theorem 3.1 (see [15, Cor. 3.1]), (3.2); f from (3.1), p. 796

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest

theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (Δ : ℝ) (hCV : CVBound P Pr Δ)
    (pol : (V → ℝ) → (V → ℝ)) (hpol : IsComparator A m P Pr pol) (W : Finset V) :
    f (fun j => ∫ ω, P j ω ∂Pr) m Δ W ≤
      ∑ j ∈ W, (∫ ω, P j ω ∂Pr) * ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.InForest
