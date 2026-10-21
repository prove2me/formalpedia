-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_5
-- name    : StochLoadBal.Makespan.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:32.718279+00:00
-- url     : https://prove2.me/theorems/df5c4644-05b7-47f9-a04a-415ecf073305
-- title:
--   Lemma 5, corrected (constant c₀ in place of 1) — new valid inequalities (3) and (4) with O(1) = 17
-- statement:
--   There is an absolute constant $c_0>0$ with the following property. Consider an instance of stochastic load balancing on $m\ge1$ unrelated machines: sizes $X_{ij}\ge0$, measurable and integrable, with the jobs independent (the vectors $(X_{ij})_{i\in[m]}$, $j\in[n]$, are independent). Let $\sigma$ assign the jobs $J_i$ to machine $i$. If
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_{ij}\Big]\ \le\ c_0,$$
--   then
--   $$\sum_{i=1}^m\sum_{j\in J_i}\mathbb E[X''_{ij}]\ \le\ 2\qquad(3)$$
--   and, for every nonempty $K\subseteq[m]$ with $k=|K|$,
--   $$\sum_{i\in K}\sum_{j\in J_i}\beta_k(X'_{ij})\ \le\ 17\,k.\qquad(4)$$
--
--   These are the valid inequalities behind the LP (5)–(9): an assignment of small expected makespan gives a feasible integral LP solution with $b=17$.
--
--   **Formalization Note** This statement is corrected. The page assumes expected makespan at most $1$; with that threshold (3) is false: on $1000$ identical machines with one job per machine, each job of size $1.02$ with probability $0.0035$ and $0$ otherwise, the expected makespan is about $0.989$, but $\sum_j\mathbb E[X''_j]\approx 3.57$. The threshold is an absolute constant $c_0$ (the proof via Lemmas 1 and 4 gives any $c_0<\min(1/2,c_1)$). The $O(1)$ of (4) is the $17$ of Lemma 4. Sizes of one job on different machines may be dependent.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 9, Lemma 5 (eqs. (3)–(4))

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 5 (New Valid Inequalities, p. 9), corrected: the threshold `1` on the expected
makespan is replaced by an absolute constant `c₀ > 0` (with `1`, inequality (3) is false), and
the `O(1)` of (4) is `17`. If an assignment `σ` has expected makespan at most `c₀`, then
(3) `Σ_i Σ_{j ∈ J_i} E[X''_{ij}] ≤ 2` and
(4) `Σ_{i ∈ K} Σ_{j ∈ J_i} β_k(X'_{ij}) ≤ 17 k` for every nonempty `K ⊆ [m]`, `k = |K|`. -/
theorem lemma_5 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin m → Fin n → Ω → ℝ),
        (∀ i j, Measurable (X i j)) → (∀ i j ω, 0 ≤ X i j ω) →
        (∀ i j, Integrable (X i j) P) → iIndepFun (fun j ω i => X i j ω) P →
        ∀ σ : Fin n → Fin m, expMakespan P X σ ≤ c₀ →
          (∑ j, ∫ ω, exc (X (σ j) j ω) ∂P ≤ 2) ∧
          ∀ K : Finset (Fin m), K.Nonempty →
            ∑ i ∈ K, ∑ j ∈ Finset.univ.filter (fun j => σ j = i),
                effSize P K.card (fun ω => trunc (X i j ω)) ≤ 17 * (K.card : ℝ) := by sorry

end StochLoadBal.Makespan
