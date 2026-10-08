-- Prove2me | Theorems.Thm_PoAIndep_Topology_lemma_3_7
-- name    : PoAIndep.Topology.lemma_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:12.07792+00:00
-- url     : https://prove2.me/theorems/b4abdb5e-e434-422c-b0c0-13993c5627f6
-- title:
--   Lemma 3.7, p. 12 — a Nash flow is a min-cost flow for the costs ℓₑ(fₑ): Σₑ ℓₑ(fₑ)fₑ ≤ Σₑ ℓₑ(fₑ)f*ₑ
-- statement:
--   Let $(G,r,\ell)$ be an instance, let $f$ be a feasible flow at Nash equilibrium and let $f^*$ be any feasible flow. Then
--   $$\sum_{e\in E}\ell_e(f_e)\,f_e\le\sum_{e\in E}\ell_e(f_e)\,f^*_e .$$
--
--   That is, a Nash flow is a minimum-cost flow, in the classical sense, for the fixed edge costs $\ell_e(f_e)$. In Theorem 3.8 it shows that the error term $\sum_e(f^*_e-f_e)\ell_e(f_e)$ is nonnegative.
--
--   **Formalization Note.** The page says "$f$ be at Nash equilibrium and $f^*$ feasible for instance $(G,r,\ell)$"; the formal statement reads "feasible" as applying to $f$ as well, since the proof invokes Proposition 2.3, which requires it, and the inequality fails for a Nash flow routing larger rates.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 12, Lemma 3.7

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem lemma_3_7 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (I : Instance V E) (f g : Flow I) (hf : IsFlow I f) (hfeas : IsFeasible I f)
    (hnash : IsNashFlow I f) (hg : IsFlow I g) (hgfeas : IsFeasible I g) :
    ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e ≤
      ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e := by sorry

end PoAIndep.Topology
