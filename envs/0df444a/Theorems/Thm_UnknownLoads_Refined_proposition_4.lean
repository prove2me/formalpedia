-- Prove2me | Theorems.Thm_UnknownLoads_Refined_proposition_4
-- name    : UnknownLoads.Refined.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:59.479295+00:00
-- url     : https://prove2.me/theorems/5e6d2a38-ebb9-47da-b3ea-057bc981b5df
-- title:
--   Proposition 4 — almost surely, 𝒜ₙ, 𝒟ₙ and qₙ are relatively compact with Lipschitz subsequential limits
-- statement:
--   For the coupled sequence of systems, there is a set $\Gamma_T$ of probability one such that for each $\omega\in\Gamma_T$ the sequences $\{\mathcal A_n(\omega):n\ge1\}$, $\{\mathcal D_n(\omega):n\ge1\}$ and $\{q_n(\omega):n\ge1\}$ are relatively compact in $D_{\mathbb R^{\mathbb N}}[0,T]$ with respect to the metric of uniform convergence
--   $$
--   \varrho(x,y)=\sup_{t\in[0,T]}\sum_{i=0}^\infty\frac{\min\{|x(t,i)-y(t,i)|,1\}}{2^i},
--   $$
--   and the limit of every convergent subsequence has Lipschitz coordinates.
--
--   This is the compactness step of the fluid-limit method: every later pathwise argument extracts a convergent subsequence through it.
--
--   **Formalization Note** Relative compactness is stated sequentially: every subsequence has a further subsequence converging uniformly on $[0,T]$ in every coordinate (equivalent to $\varrho$-convergence, p. 46), and every coordinatewise uniform limit along a subsequence is Lipschitz on $[0,T]$ in every coordinate. The statement holds for every sequence $\alpha_n\in(0,1)$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 25, Proposition 4

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_PoissonProcess
import Definitions.Def_UnknownLoads_Refined_Load
import Definitions.Def_UnknownLoads_Refined_Construction
import Definitions.Def_UnknownLoads_Refined_System

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace UnknownLoads.Refined

theorem proposition_4 (D : LoadData) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α : ℕ → ℝ}
    (sys : System D Ω P α) :
    ∀ᵐ ω ∂P,
      IsRelCompactLip D.T (fun n => sys.arr n ω) ∧
      IsRelCompactLip D.T (fun n => sys.dep n ω) ∧
      IsRelCompactLip D.T (fun n => sys.q n ω) := by sorry

end UnknownLoads.Refined
