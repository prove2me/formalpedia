-- Prove2me | Theorems.Thm_UnknownLoads_Refined_lemma_5
-- name    : UnknownLoads.Refined.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:00.886076+00:00
-- url     : https://prove2.me/theorems/9d6db597-c03f-4ca3-8ab5-9989ec235fe1
-- title:
--   Lemma 5 — eventually no pool has more than B_T tasks and ℓₙ ≤ B_T on [0, T], almost surely
-- statement:
--   For the coupled sequence of systems, there is a constant $B_T\in\mathbb N$, $B_T>0$, such that with probability one
--   $$
--   q_n(t,B_T+1)=0\qquad\text{and}\qquad \ell_n(t)\le B_T\qquad\text{for all }t\in[0,T]
--   $$
--   and all sufficiently large $n$.
--
--   The bound keeps every occupancy state finitely supported and the threshold bounded, uniformly over time; it is part (a) of Proposition 7.
--
--   **Formalization Note** The constant comes before the almost-sure quantifier; the threshold on $n$ is inside it and may depend on the outcome. The statement holds for every sequence $\alpha_n\in(0,1)$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 26, Lemma 5

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem lemma_5 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α) :
    ∃ BT : ℕ, 0 < BT ∧ ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc 0 D.T,
      sys.q n ω t (BT + 1) = 0 ∧ sys.ℓ n ω t ≤ BT := by sorry

end UnknownLoads.Refined
