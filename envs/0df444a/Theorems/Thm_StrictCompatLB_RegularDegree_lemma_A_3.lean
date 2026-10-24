-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_3
-- name    : StrictCompatLB.RegularDegree.lemma_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:05.217604+00:00
-- url     : https://prove2.me/theorems/35452683-6b30-4b32-a4ee-ef2680d5006c
-- title:
--   Lemma A.3 — a.s. eventually at most δM(N) dispatchers have degree ≤ (1 − ε)E|N_w|
-- statement:
--   In the random graph model of Theorem 3.5 (each of the $N$ servers picks $c(N)\le M(N)$ of the $M(N)$ dispatchers uniformly without replacement, independently over servers), let $\mathcal N_w$ be the set of servers adjacent to dispatcher $w$; its mean size is $\mathbb E|\mathcal N_w|=Nc(N)/M(N)$. For $\varepsilon>0$ let
--   $$A_N=\{w\in W_N:|\mathcal N_w|\le(1-\varepsilon)\,\mathbb E|\mathcal N_w|\}.$$
--   Assume $c(N)\to\infty$ and $Nc(N)/M(N)\to\infty$. Then for all $\varepsilon>0$ and $\delta>0$, almost surely there exists $N_0\ge1$ such that
--   $$|A_N|\le\delta M(N)\qquad\text{for all }N\ge N_0 .$$
--
--   So almost surely all but a vanishing fraction of the dispatchers have degree at least a fixed fraction of its mean. Proposition A.4 uses this to restrict proportional sparsity to the remaining dispatchers.
--
--   **Formalization Note** $\mathbb E|\mathcal N_w|$ is written out as $Nc(N)/M(N)$, its value under the model's law.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 32, Lemma A.3, (A.7)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree

theorem lemma_A_3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((lowDegreeDispatchers M c (randomGraph M adj ω) ε N).card : ℝ) ≤ δ * (M N : ℝ) := by sorry

end StrictCompatLB.RegularDegree
