-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_theorem_3_1
-- name    : StochSchedPrec.CMNS.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:32.569362+00:00
-- url     : https://prove2.me/theorems/613f451d-d7af-4cd7-872e-557864f90d44
-- title:
--   Theorem 3.1, p. 797 — load inequalities Σ_{j∈W} E[P_j] E[C^Π_j] ≥ f(W) for every nonanticipatory policy
-- statement:
--   Consider $m\ge1$ machines, acyclic precedence constraints, release dates $r_j\ge0$ and independent nonnegative processing times $P_j$ whose coefficients of variation are bounded by $\sqrt\Delta$ for some $\Delta\ge0$. Let $\Pi$ be any feasible nonanticipatory scheduling policy with integrable completion times $C^\Pi_j(P)$. Then for every $W\subseteq V$
--   $$\sum_{j\in W}\mathrm E[P_j]\,\mathrm E[C^\Pi_j(P)]\ge f(W),$$
--   with $f$ the set function (3.1).
--
--   These load inequalities, due to Möhring, Schulz and Uetz (J. ACM 1999, Cor. 3.1), are the polyhedral lower bound on which the LP relaxation of §3 rests.
--
--   **Formalization Note** Assumption 2.1 plays no role and is dropped. Comparator policies are required to have integrable completion times; a policy with $\mathrm E[C^\Pi_j]=\infty$ satisfies any upper bound against it trivially, and the requirement prevents the Bochner integral from returning its default value $0$. Comparator policies are also required to be measurable for the law of $P$ (almost everywhere equal to a Borel map): §5, p. 800, requires every policy to be a universally measurable map, which implies this. Without it a non-measurable policy on a suitably enlarged probability space can correlate its decisions with unobserved processing times, and the load inequalities fail.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, Theorem 3.1 (citing Möhring, Schulz, Uetz, J. ACM 46 (1999), Cor. 3.1), eq. (3.2) with (3.1) p. 796

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) (W : Finset V) :
    loadFn m Δ (fun j => ∫ ω, P j ω ∂Pr) W
      ≤ ∑ j ∈ W, (∫ ω, P j ω ∂Pr) * ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.CMNS
