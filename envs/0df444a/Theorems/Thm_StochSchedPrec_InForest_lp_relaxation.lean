-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_lp_relaxation
-- name    : StochSchedPrec.InForest.lp_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:31.297078+00:00
-- url     : https://prove2.me/theorems/4f1e1b50-8259-42cc-b55f-3cb6fe2e2806
-- title:
--   §3, p. 797 — expected completion times of any nonanticipatory policy are feasible for the LP-relaxation
-- statement:
--   In the setting of Theorem 3.1 (acyclic precedence constraints $A$, $m\ge 1$ machines, no release dates, independent nonnegative processing times with $\mathrm{CV}[P_j]\le\sqrt\Delta$, nonnegative weights $w_j$), let $\Pi$ be a feasible nonanticipatory policy with integrable completion times $C^\Pi_j(P)$. Then the vector $C_j=\mathrm E[C^\Pi_j(P)]$ satisfies all constraints of the LP-relaxation,
--   $$\sum_{j\in W}\mathrm E[P_j]\,C_j\ge f(W)\ (W\subseteq V),\qquad C_j\ge C_i+\mathrm E[P_j]\ ((i,j)\in A),\qquad C_j\ge\mathrm E[P_j]\ (j\in V),$$
--   and its LP objective equals the policy's expected cost:
--   $$\sum_{j\in V}w_j\,\mathrm E[C^\Pi_j(P)]=\mathrm E\Big[\sum_{j\in V}w_jC^\Pi_j(P)\Big].$$
--
--   Hence the LP-relaxation's optimal value is a lower bound on the expected cost of every nonanticipatory policy.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, §3, paragraph "Observe that under any scheduling policy Π the trivial inequalities" and the LP-relaxation display

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest

theorem lp_relaxation {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (w : V → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (Δ : ℝ) (hCV : CVBound P Pr Δ)
    (pol : (V → ℝ) → (V → ℝ)) (hpol : IsComparator A m P Pr pol) :
    IsLPFeasible (fun j => ∫ ω, P j ω ∂Pr) A m Δ
        (fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr) ∧
      ∑ j, w j * ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr =
        ∫ ω, (∑ j, w j * (pol (fun k => P k ω) j + P j ω)) ∂Pr := by sorry

end StochSchedPrec.InForest
