-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_critical_chain_lower_bound
-- name    : StochSchedPrec.CMNS.critical_chain_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:19.669367+00:00
-- url     : https://prove2.me/theorems/b43636c2-2677-4629-9c8d-71dd28110172
-- title:
--   §4, p. 798 — the critical-chain length ℓ_j(p) is a lower bound on C_j, and E[ℓ_j(P)] on E[C^Π_j] for every policy
-- statement:
--   Consider $m\ge1$ machines, acyclic precedence constraints, release dates $r_j\ge0$ and a fixed tie-breaking order for critical predecessors.
--   1. For every realization $p\ge0$, every schedule $S$ from which the critical chain is taken, and every feasible schedule $S'$ for $p$, the critical chain length is at most the completion time in $S'$: $\ell_j(p)\le S'_j+p_j$.
--   2. Consequently, in the standing stochastic model, if $\sigma$ is a measurable schedule map (such as the CMNS policy) and $\Pi$ any feasible nonanticipatory policy with integrable completion times, then
--   $$\mathrm E[\ell_j(P)]\le\mathrm E[C^\Pi_j(P)]\qquad\text{for every job }j,$$
--   where $\ell_j(P)$ is the critical chain length of $j$ in the schedule $\sigma(P)$.
--
--   The critical chain is a precedence chain starting at a release date, so its length bounds the completion time of $j$ in any feasible schedule. Since the chain depends on the realization, this lower bound cannot be obtained from the precedence constraints of the LP.
--
--   **Formalization Note** The paper states the bound for the CMNS schedule's own completion times and for every policy; the first part here holds for the critical chain taken from any schedule $S$.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 798, proof of Theorem 4.1, paragraph "Now, for any job j"

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem critical_chain_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (tb : V ≃ Fin (Fintype.card V)) :
    (∀ (p S S' : V → ℝ), (∀ j, 0 ≤ p j) → IsFeasible m A r p S' →
        ∀ j, chainLength A r tb p S j ≤ S' j + p j) ∧
      ∀ (P : V → Ω → ℝ), IsStochModel Pr P →
        ∀ (σ : (V → ℝ) → V → ℝ), AEMeasurable (fun ω => σ (fun k => P k ω)) Pr →
        ∀ (pol : (V → ℝ) → V → ℝ), IsAdmissiblePolicy m A r Pr P pol →
        ∀ j, ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr
          ≤ ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by sorry

end StochSchedPrec.CMNS
