-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_lp_relaxation
-- name    : StochSchedPrec.CMNS.lp_relaxation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:30.891402+00:00
-- url     : https://prove2.me/theorems/00025433-fe2b-4541-8d1a-a255962af196
-- title:
--   §3, p. 797 — the expected completion times of any nonanticipatory policy are LP-feasible, so the LP optimum is a lower bound
-- statement:
--   Under the assumptions of Theorem 3.1 (independent nonnegative processing times with $\mathrm{CV}[P_j]\le\sqrt\Delta$, $\Delta\ge0$; release dates $r_j\ge0$; weights $w_j\ge0$), let $\Pi$ be any feasible nonanticipatory policy with integrable completion times. Then the vector $\big(\mathrm E[C^\Pi_j(P)]\big)_{j\in V}$ satisfies all constraints of the LP relaxation
--   $$\sum_{j\in W}\mathrm E[P_j]\,C_j\ge f(W)\ (W\subseteq V),\qquad C_j\ge C_i+\mathrm E[P_j]\ ((i,j)\in A),\qquad C_j\ge\mathrm E[P_j]\ (j\in V),$$
--   and consequently every optimal solution $C^{\mathrm{LP}}$ of the LP satisfies
--   $$\sum_{j\in V}w_jC^{\mathrm{LP}}_j\le\mathrm E\Big[\sum_{j\in V}w_jC^\Pi_j(P)\Big].$$
--
--   The LP is therefore a relaxation of $\mathrm P\,|\,r_j,\mathit{prec}\,|\,\mathrm E[\sum w_jC_j]$, and its optimal value is a lower bound on the expected cost of every nonanticipatory policy.
--
--   **Formalization Note** As in Theorem 3.1, comparator policies have integrable completion times and are measurable for the law of $P$ (§5, p. 800, requires universal measurability of every policy).
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, §3, paragraph "Observe that under any scheduling policy Π" and the LP relaxation

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem lp_relaxation {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r w : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) :
    IsLPFeasible m A Δ (fun j => ∫ ω, P j ω ∂Pr)
        (fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr) ∧
      ∀ C : V → ℝ, IsLPOptimal m A Δ (fun j => ∫ ω, P j ω ∂Pr) w C →
        ∑ j, w j * C j ≤ ∫ ω, ∑ j, w j * (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.CMNS
