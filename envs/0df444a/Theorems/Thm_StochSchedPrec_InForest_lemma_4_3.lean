-- Prove2me | Theorems.Thm_StochSchedPrec_InForest_lemma_4_3
-- name    : StochSchedPrec.InForest.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:19.048186+00:00
-- url     : https://prove2.me/theorems/96cfeb39-1a98-49ea-ae20-212cb2428fa6
-- title:
--   Lemma 4.3, p. 799 — Graham's schedule processes no job of A_j in [r_j(p), S_j(p)[ for in-forests
-- statement:
--   Let the precedence constraints $A$ on the job set $V$ form an acyclic in-forest (each job has at most one successor), let $m\ge 1$, and let $L$ be a priority list that is a linear extension of the precedence constraints. Let $p\ge 0$ be any realization of the processing times and $S$ the schedule constructed by Graham's list scheduling with list $L$ on $m$ machines (no release dates). For a job $j$ let $r_j(p)$ be the earliest time at which $j$ is available, and $A_j$ the set of jobs after $j$ in $L$. Then no job of $A_j$ is in process during $[r_j(p),S_j(p)[$:
--   $$\forall k\in A_j\ \ \forall t\in[r_j(p),S_j(p)[:\qquad \neg\,\big(S_k\le t<S_k+p_k\big).$$
--
--   The lemma is the in-forest substitute for deliberate idle time: in the interval where $j$ waits, the machines are occupied only by jobs of higher priority. It drives the per-realization completion-time bound of Lemma 4.4.
--
--   **Formalization Note** Zero processing times are allowed ($p_j\ge 0$), as in the paper.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 799, Lemma 4.3

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham

namespace StochSchedPrec.InForest

theorem lemma_4_3 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsLinearExtension A L)
    (p : V → ℝ) (hp : IsNonneg p) (S : V → ℝ) (hS : IsGraham A m L p S)
    (j k : V) (hk : k ∈ Aset L j) (t : ℝ) (ht₁ : availTime A p S j ≤ t) (ht₂ : t < S j) :
    ¬ (S k ≤ t ∧ t < S k + p k) := by sorry

end StochSchedPrec.InForest
