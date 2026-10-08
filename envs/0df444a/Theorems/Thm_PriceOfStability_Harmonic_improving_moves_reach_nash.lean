-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_improving_moves_reach_nash
-- name    : PriceOfStability.Harmonic.improving_moves_reach_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:09.418773+00:00
-- url     : https://prove2.me/theorems/750de041-915a-46ee-9e00-98ace880a480
-- title:
--   Theorem 2.1, proof — improving moves reach a Nash equilibrium of no larger potential
-- statement:
--   Let $G$ be a congestion game on finitely many players and resources, with Rosenthal potential $\Phi$. For every strategy profile $S_0$ (each player using one of its feasible strategies) there is a pure Nash equilibrium $S$ with
--   $$\Phi(S)\le\Phi(S_0).$$
--
--   A pure Nash equilibrium is a profile in which no player can lower its cost by switching to another of its feasible strategies. In the paper this is the end point of a sequence of improving moves started at $S_0$; it is the step that turns the potential into existence of a cheap equilibrium.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1607 (PDF p. 6), Theorem 2.1, proof

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, proof, p. 1607 (PDF p. 6): starting from any strategy vector, a sequence of
improving moves leads to a Nash equilibrium, each move decreasing the potential `Φ` of (2.1); so
from every profile `S₀` there is a pure Nash equilibrium `S` with `Φ(S) ≤ Φ(S₀)`.

**Formalization Note.** Stated for every congestion game. The conclusion is the existence of the
end point of the improving sequence, with its potential bound, which is what the proofs of
Theorems 2.1, 2.3 and 3.1 use. -/
theorem improving_moves_reach_nash {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S₀ : ι → Finset E) (h₀ : IsProfile G S₀) :
    ∃ S, IsPureNash G S ∧ potential G S ≤ potential G S₀ := by sorry

end PriceOfStability.Harmonic
