-- Prove2me | Theorems.Thm_TIESharp_seven_preliminaries_normalized
-- name    : TIESharp.seven_preliminaries_normalized
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:52:25.891046+00:00
-- url     : https://prove2.me/theorems/c82a4d58-9e17-405a-9735-6c7de6e64527
-- title:
--   Seven-machine normalized selector preliminaries
-- statement:
--   Normalize $n=7$ and $T=\mathrm{OPT}(t)=1$. Let $y$ be the slot law, choose a maximum-load machine $I(A)$ in every outcome, and put $\theta_i=\Pr(I=i)$. Then $\theta\ge0$, $\sum_i\theta_i=1$, and $\|\theta\|_2\le1$. Moreover:
--   * if $\|\theta\|_2\le3/4$ or $\|\theta\|_2=1$, then $\mathbb E[C_{\max}]\le4$;
--   * an optimal integral assignment exists;
--   * $d_i\le2$ for every machine; and
--   * if $d_i>1$, there is a job $j$ with $q_{ij}>0$ and $t_{ij}=d_i$.
--
--   The last two assertions come from Lemma 5.2 and the definition of $d_i$. The existence assertion merely selects a minimizer on the finite set of assignments, which is nonempty because there are seven machines.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Proposition 5.5 proof, first three paragraphs of p.27; Lemma 5.2, p.23, for d_i≤2T and the supported-job witness.

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw
import Definitions.Def_TIESharp_dMax
import Definitions.Def_TIESharp_selProb

set_option autoImplicit false

/-- The selector normalization, the two elementary selector-norm cases, and the supported-job
witness used at the start of the seven-machine proof (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Proposition 5.5, p.27, using Lemma 5.2). -/
theorem TIESharp.seven_preliminaries_normalized (m : ℕ) (t : Fin 7 → Fin m → ℝ)
    (ht : TIESharp.Nonneg t) (hT : TIESharp.opt t = 1)
    (y : (Fin m → Fin 7) → ℝ) (hy : TIESharp.IsBSSlotLaw t y)
    (sel : (Fin m → Fin 7) → Fin 7)
    (hsel : ∀ A, MatousekLP.Scheduling.load (Matrix.of t) A (sel A)
      = MatousekLP.Scheduling.makespan (Matrix.of t) A) :
    (∀ i, 0 ≤ TIESharp.selProb y sel i) ∧ (∑ i, TIESharp.selProb y sel i) = 1 ∧
    Real.sqrt (∑ i, TIESharp.selProb y sel i ^ 2) ≤ 1 ∧
    (Real.sqrt (∑ i, TIESharp.selProb y sel i ^ 2) ≤ 3 / 4 ∨
      Real.sqrt (∑ i, TIESharp.selProb y sel i ^ 2) = 1 →
        ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 4) ∧
    (∃ Astar : Fin m → Fin 7,
      MatousekLP.Scheduling.IsOptimalSchedule (Matrix.of t) Astar) ∧
    (∀ i, TIESharp.dMax t i ≤ 2) ∧
    (∀ i, 1 < TIESharp.dMax t i →
      ∃ j, 0 < TIESharp.bsProb t i j ∧ t i j = TIESharp.dMax t i) := by sorry
