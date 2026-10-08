-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_rosenthal_potential_change
-- name    : PriceOfStability.Harmonic.rosenthal_potential_change
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:27.523225+00:00
-- url     : https://prove2.me/theorems/8fc04948-d950-482a-99e8-b26f31a03742
-- title:
--   Theorem 2.1, proof, (2.1) — Rosenthal's function is an exact potential
-- statement:
--   Let $G$ be a congestion game on a finite set of players and a finite set $E$ of resources, where a resource $e$ used by $x$ players costs each of them $f_e(x)$, and player $i$ pays $c_i(S)=\sum_{e\in S_i} f_e(x_e)$. Rosenthal's potential is
--   $$\Phi(S)=\sum_{e\in E}\sum_{x=1}^{x_e} f_e(x).$$
--   If a single player $i$ changes its strategy from $S_i$ to $T$, giving $S'=(S_1,\dots,T,\dots,S_k)$, then
--   $$\Phi(S')-\Phi(S)=c_i(S')-c_i(S).$$
--
--   The change in the potential tracks exactly the change in the deviating player's cost, which is what makes congestion games potential games.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1607 (PDF p. 6), Theorem 2.1, proof, (2.1)

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, proof, (2.1), p. 1607 (PDF p. 6): Rosenthal's function
`Φ(S) = Σ_{e∈E} Σ_{x=1}^{x_e} f_e(x)` is an exact potential — when a single player `i` deviates
from `S` to `S′ = (S₋ᵢ, T)`, the change of `Φ` equals the change of player `i`'s cost.

**Formalization Note.** Stated for every congestion game (arbitrary latencies `f_e`, arbitrary
strategy families) and every deviation, as on the page. -/
theorem rosenthal_potential_change {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (i : ι) (T : Finset E) :
    potential G (Function.update S i T) - potential G S =
      cost G (Function.update S i T) i - cost G S i := by sorry

end PriceOfStability.Harmonic
