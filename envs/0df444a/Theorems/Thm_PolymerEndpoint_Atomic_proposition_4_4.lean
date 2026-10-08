-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_proposition_4_4
-- name    : PolymerEndpoint.Atomic.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:01.135153+00:00
-- url     : https://prove2.me/theorems/cad57998-3605-439f-bfed-516576be3f84
-- title:
--   Proposition 4.4 — fixed points of 𝒯 charge only states of mass 0 or 1
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$. Write $\|f\|=\sum_u f(u)$ for the total mass of a partitioned subprobability measure $f\in\mathcal S$, and let $\mathcal K$ be the set of probability measures on $\mathcal S$ fixed by the update map $\mathcal T$ (4.5). If $\nu\in\mathcal K$, then
--
--   $$
--   \nu\bigl(\{f\in\mathcal S:0<\|f\|<1\}\bigr)=0.
--   $$
--
--   Every invariant law lives on the states of mass $0$ and mass $1$; this dichotomy drives the characterization of the low-temperature phase in Theorem 5.2.
--
--   **Formalization Note** The positivity $\beta>0$ is the paper's standing assumption (§1.1, p. 4); the proof's strict Jensen step uses that $\sum_u\sum_{v\sim u}f(v)e^{\beta Y_u}$ is not almost surely constant, which needs $\beta>0$ and the non-degeneracy of $\mathfrak L$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 33, Proposition 4.4

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem proposition_4_4 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    (ν : Measure (PSM d)) (hν : ν ∈ K (d := d) 𝔏 β) :
    ν {f : PSM d | 0 < mass f ∧ mass f < 1} = 0 := by sorry

end PolymerEndpoint.Atomic
