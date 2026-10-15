-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_proposition_A_4
-- name    : StrictCompatLB.RegularDegree.proposition_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:54.544983+00:00
-- url     : https://prove2.me/theorems/7bb81a1d-cd4b-4cbf-b08d-860902086428
-- title:
--   Proposition A.4 — server-regular random graphs with c(N) → ∞ and Nc(N)/M(N) → ∞ are a.s. proportionally sparse
-- statement:
--   In the random graph model of Theorem 3.5, each of the $N$ servers picks $c(N)\le M(N)$ of the $M(N)$ dispatchers uniformly at random without replacement, independently over servers. Nothing is assumed about the joint law across $N$. Assume
--   $$c(N)\to\infty\qquad\text{and}\qquad \frac{Nc(N)}{M(N)}\to\infty .$$
--   Then almost surely the graph sequence $\{G_N\}_{N\ge1}$ is proportionally sparse: for every $\varepsilon>0$,
--   $$\sup_{U\subseteq V_N}\Big|\Big\{w\in W_N:\Big|\frac{|\mathcal N_w\cap U|}{|\mathcal N_w|}-\frac{|U|}{N}\Big|\ge\varepsilon\Big\}\Big|\Big/M(N)\to0 .$$
--
--   This is the first of the two graph conditions in Theorem 3.5.
--
--   **Formalization Note** Proportional sparsity is the limit condition (3.1) without the connectivity in Definition 3.1, as in the mission's definition file. A dispatcher with no neighbours contributes the ratio $0/0$, evaluated as $0$.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 32, Proposition A.4

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree

theorem proposition_A_4
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (randomGraph M adj ω) := by sorry

end StrictCompatLB.RegularDegree
