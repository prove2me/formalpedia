-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_theorem_4_1
-- name    : StochSchedPrec.CMNS.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:28.788643+00:00
-- url     : https://prove2.me/theorems/c35199af-4663-4df0-b06c-b1defbb73684
-- title:
--   Theorem 4.1, p. 798 — CMNS with an LP-optimal priority list is a (1+β)(1+1/β+max{1,(m−1)Δ/m})-approximation for P|r_j, prec|E[Σ w_j C_j]
-- statement:
--   Consider an instance of the stochastic machine scheduling problem $\mathrm P\,|\,r_j,\mathit{prec}\,|\,\mathrm E[\sum w_jC_j]$: $m\ge1$ identical machines, acyclic precedence constraints, release dates $r_j\ge0$ satisfying Assumption 2.1, weights $w_j\ge0$, and independent nonnegative processing times $P_j$ with $\mathrm{CV}[P_j]\le\sqrt\Delta$ for all $j$ and some $\Delta\ge0$. Let $C^{\mathrm{LP}}$ be an optimal solution of the LP relaxation of §3, let $L$ be a priority list according to nondecreasing $C^{\mathrm{LP}}_j$, let $\beta>0$, and let $\sigma$ be the policy given by Algorithm CMNS with list $L$ and thresholds $\beta\,\mathrm E[P_j]$. Then the expected cost of CMNS is finite and, for every feasible nonanticipatory scheduling policy $\Pi$ with integrable completion times,
--   $$\mathrm E\Big[\sum_{j\in V}w_jC^{\mathrm{CMNS}}_j(P)\Big]\le\alpha\;\mathrm E\Big[\sum_{j\in V}w_jC^\Pi_j(P)\Big],\qquad \alpha=(1+\beta)\Big(1+\frac1\beta+\max\Big\{1,\frac{m-1}m\Delta\Big\}\Big).$$
--   In particular CMNS is an $\alpha$-approximation. For NBUE processing times one may take $\Delta=1$, and $\beta=1/\sqrt2$ gives $\alpha=3+2\sqrt2$.
--
--   **Formalization Note** The comparison is against every admissible policy, which implies the paper's comparison with an optimal policy and does not presuppose that one exists. Nonanticipation and measurability of the CMNS policy are the paper's assertions (p. 795; §5, p. 800), taken as hypotheses; measurability, of the CMNS policy and of the comparators, means measurability for the law of $P$, which §5's universal measurability of every policy implies. The fact that the LP order is a linear extension of the precedence constraints is not assumed: it follows from $\mathrm E[P_j]>0$ and the arc constraints of the LP.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 798, Theorem 4.1

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem theorem_4_1 {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r w : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hw : ∀ j, 0 ≤ w j)
    (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hCV : HasCVBound Pr P Δ)
    (C : V → ℝ) (hC : IsLPOptimal m A Δ (fun j => ∫ ω, P j ω ∂Pr) w C)
    (L : Fin (Fintype.card V) ≃ V) (hL : IsSortedBy L C) (β : ℝ) (hβ : 0 < β)
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω)))
    (pol : (V → ℝ) → V → ℝ) (hpol : IsAdmissiblePolicy m A r Pr P pol)
    (hpolm : AEMeasurable pol (Pr.map (fun ω k => P k ω))) :
    Integrable (fun ω => ∑ j, w j * (σ (fun k => P k ω) j + P j ω)) Pr ∧
    ∫ ω, ∑ j, w j * (σ (fun k => P k ω) j + P j ω) ∂Pr
      ≤ (1 + β) * (1 + 1 / β + max 1 (((m : ℝ) - 1) / m * Δ))
          * ∫ ω, ∑ j, w j * (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.CMNS
