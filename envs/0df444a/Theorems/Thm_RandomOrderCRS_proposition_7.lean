-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_7
-- name    : RandomOrderCRS.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:46.029066+00:00
-- url     : https://prove2.me/theorems/c619fa86-c810-4ab7-b335-efc8d6e4b931
-- title:
--   Proposition 7 — survival and blocked neighbours imply selection
-- statement:
--   Let $Y$ have distinct coordinates. If $e$ survives, $|\mathcal R_e|\le1$, and each $f\in\mathcal R_e$ satisfies $\mathrm{sbl}_f$, then $e\in\mathcal M$.
--
--   This is the event that the lower bound on the selection probability counts.
--
--   Differences from the source:
--   - encoding: the statement on the sample space → pathwise, for injective $Y$; reason: with a tie $Y_f=Y_e$, the edge $f$ is not relevant for $e$ and yet may arrive first; ties have probability 0
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 7, p.19

import Mathlib
import Definitions.Def_RandomOrderCRS_ArrivalModel
import Definitions.Def_RandomOrderCRS_SimpleBlocker

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Proposition 7, MacRury, Ma & Grammel, arXiv:2209.07520v2, p.19: "If e survives, |ℛ_e| ≤ 1, and
each f ∈ ℛ_e satisfies sbl_f, then e ∈ ℳ."

**Formalization Note.** Pathwise, for injective `Y`, i.e. almost surely. With a tie `Y_f = Y_e`, the
edge `f` is not relevant for `e` and yet may arrive first. -/
theorem proposition_7 (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (hY : Function.Injective Y) (e : G.edgeSet) (he : S e = true)
    (hcard : (relevantSet G Y S e).card ≤ 1)
    (hsbl : ∀ f ∈ relevantSet G Y S e, HasSimpleBlocker G Y S e f) :
    e ∈ greedy G (arrivalOrder G Y) S := by sorry

end RandomOrderCRS
