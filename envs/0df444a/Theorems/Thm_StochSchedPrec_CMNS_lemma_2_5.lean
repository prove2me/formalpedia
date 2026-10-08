-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_lemma_2_5
-- name    : StochSchedPrec.CMNS.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:20.777882+00:00
-- url     : https://prove2.me/theorems/dae2c083-d46e-4467-af14-e88a8605cb64
-- title:
--   Lemma 2.5, p. 794 — per-realization completion-time bound (2.1) for Algorithm CMNS
-- statement:
--   Consider an instance with $m\ge1$ machines, acyclic precedence constraints and release dates $r_j\ge0$ satisfying Assumption 2.1. Let $L$ be a priority list that is a linear extension of the precedence constraints, $\beta\ge0$, $\mu_j\ge0$, $p\ge0$ a realization, and let $S$ be the schedule constructed by Algorithm CMNS with completion times $C_j(p)=S_j+p_j$. Let $\ell_j(p)$ be the length of the critical chain of $j$ in this schedule (for a fixed tie-breaking rule). Then for every job $j$
--   $$C_j(p)\le\frac{m-1}m\,\ell_j(p)+\frac1m\,r_j+\frac1m\Big(\sum_{i\in B_j}\big(p_i+\beta\mu_i\big)+\sum_{i\in O_j(p)}p_i\Big),$$
--   where $B_j$ is the set of jobs up to and including $j$ in $L$ and $O_j(p)$ the set of jobs after $j$ in $L$ that are started before $j$.
--
--   This is the deterministic core of the analysis: after taking expectations it yields Theorem 2.8.
--
--   **Formalization Note** The paper has $\mu_j=\mathrm E[P_j]$; the bound holds for any nonnegative threshold vector.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 794, Lemma 2.5, eq. (2.1)

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem lemma_2_5 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L)
    (β : ℝ) (hβ : 0 ≤ β) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (tb : V ≃ Fin (Fintype.card V))
    (p : V → ℝ) (hp : ∀ j, 0 ≤ p j) (S : V → ℝ) (hS : IsCMNSRun m A r L β μ p S) (j : V) :
    S j + p j ≤ ((m : ℝ) - 1) / m * chainLength A r tb p S j + 1 / (m : ℝ) * r j
      + 1 / (m : ℝ) * (∑ i ∈ before L j, (p i + β * μ i) + ∑ i ∈ outOfOrder L S j, p i) := by sorry

end StochSchedPrec.CMNS
