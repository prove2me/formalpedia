-- Prove2me | Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_5
-- name    : StrictCompatLB.RegularDegree.lemma_A_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:08:03.337201+00:00
-- url     : https://prove2.me/theorems/5f103433-c0b6-4d05-8578-bbbbab51875e
-- title:
--   Lemma A.5 — server-regular random graphs with Nc(N)/(M(N) ln N) → ∞ satisfy (A.19) almost surely
-- statement:
--   In the random graph model of Theorem 3.5, each of the $N$ servers picks $c(N)$ of the $M(N)$ dispatchers uniformly at random without replacement, independently over servers, with $1\le c(N)\le M(N)$. Nothing is assumed about the joint law across $N$. Assume
--   $$c(N)=\omega\Big(\frac{M(N)\ln N}{N}\Big),\qquad\text{i.e.}\qquad \frac{Nc(N)}{M(N)\ln N}\to\infty .$$
--   Then almost surely the graph sequence satisfies
--   $$\limsup_{N\to\infty}\max_{v\in V_N}\frac{N}{M(N)}\sum_{w\in W_N}\frac{\mathbb 1\{(v,w)\in E_N\}}{|\mathcal N_w|}\le1. \tag{A.19}$$
--
--   Together with the reduction (A.19) $\Rightarrow$ (3.2), this gives the subcriticality half of Theorem 3.5.
--
--   **Formalization Note** Lemma A.5 reads "satisfies (A.19), and hence the subcriticality condition, almost surely". Only the (A.19) part is stated here; the "hence" is the separate deterministic reduction milestone. $\limsup\le1$ is written as "for every $\varepsilon>0$, eventually every server's value is at most $1+\varepsilon$". Since $\ln 1=0$, the ratio is $0$ at $N=1$ (Lean's division by zero); this does not affect the limit.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 34, Lemma A.5, (A.19)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree

theorem lemma_A_5
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hcM_log : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / ((M N : ℝ) * Real.log (N : ℝ)))
      atTop atTop) :
    ∀ᵐ ω ∂P, SatisfiesA19 M (randomGraph M adj ω) := by sorry

end StrictCompatLB.RegularDegree
