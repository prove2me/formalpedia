-- Prove2me | Theorems.Thm_StochSchedPrec_CMNS_lemma_3_3
-- name    : StochSchedPrec.CMNS.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:54:27.4767+00:00
-- url     : https://prove2.me/theorems/da31e965-cc5e-4166-8c73-b743245ba415
-- title:
--   Lemma 3.3, p. 797 — (1/m) Σ_{k≤j} E[P_k] ≤ (1 + max{1, (m−1)Δ/m}) C^LP_j for points sorted by C^LP
-- statement:
--   Let $m\ge1$, $\Delta\ge0$ and $\mu_j\ge0$ ($j\in V$). Let $C^{\mathrm{LP}}$ satisfy the first and the last set of inequalities of the LP relaxation,
--   $$\sum_{j\in W}\mu_jC^{\mathrm{LP}}_j\ge f(W)\quad(W\subseteq V),\qquad C^{\mathrm{LP}}_j\ge\mu_j\quad(j\in V),$$
--   and let $L$ be a list along which $C^{\mathrm{LP}}$ is nondecreasing. Then for every job $j$
--   $$\frac1m\sum_{i\in B_j}\mu_i\le\Big(1+\max\Big\{1,\frac{m-1}m\Delta\Big\}\Big)C^{\mathrm{LP}}_j,$$
--   where $B_j$ is the set of jobs up to and including $j$ in $L$.
--
--   This lemma of Möhring, Schulz and Uetz converts the load-dependent term of Theorem 2.8 into a multiple of the LP value.
--
--   **Formalization Note** The paper has $\mu_j=\mathrm E[P_j]$ and numbers the jobs so that $C^{\mathrm{LP}}_1\le\dots\le C^{\mathrm{LP}}_n$; here the numbering is a list $L$ sorted by $C^{\mathrm{LP}}$, and $\mu$ is any nonnegative vector.
-- source:
--   Skutella and Uetz, Stochastic machine scheduling with precedence constraints, SIAM J. Comput. 34(4) (2005) 788–802, p. 797, Lemma 3.3 (citing Möhring, Schulz, Uetz, J. ACM 46 (1999), Lemma 4.2)

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm

open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.CMNS

theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V]
    (m : ℕ) (hm : 0 < m) (Δ : ℝ) (hΔ : 0 ≤ Δ) (μ : V → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (C : V → ℝ) (hload : ∀ W : Finset V, loadFn m Δ μ W ≤ ∑ j ∈ W, μ j * C j)
    (hlow : ∀ j, μ j ≤ C j)
    (L : Fin (Fintype.card V) ≃ V) (hL : IsSortedBy L C) (j : V) :
    1 / (m : ℝ) * ∑ i ∈ before L j, μ i ≤ (1 + max 1 (((m : ℝ) - 1) / m * Δ)) * C j := by sorry

end StochSchedPrec.CMNS
