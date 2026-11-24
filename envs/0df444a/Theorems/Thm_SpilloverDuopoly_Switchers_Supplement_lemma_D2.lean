-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_Supplement_lemma_D2
-- name    : SpilloverDuopoly.Switchers.Supplement.lemma_D2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:40:27.579857+00:00
-- url     : https://prove2.me/theorems/89ea3291-657e-4ba5-bb0c-aaceceff2273
-- title:
--   Lemma D.2, p. 52 (PDF 54) — π_i^{kl} = 0 when neither k nor l is i
-- statement:
--   Fix a period-2 offer profile and a terminal history $(k,l)$ in the four-firm three-period game, including $l=0$. If neither earlier purchase was firm $i$'s product, then every equilibrium of that history's terminal pricing game gives firm $i$ zero profit:
--   $$k\ne i,\ l\ne i\quad\Longrightarrow\quad\pi_i^{kl}=0.$$
--   At least two untried goods remain. Demand from the selected history is per unit of its initial share $\lambda_k$. The result removes untried-history terms when deriving (31) from the original total profit.
--
--   Differences from the source:
--   - generalization: Terminal demand from the source learning game. → Any local terminal demand with nonnegativity, no demand for withdrawn offers, cheapest-only untried sales and capture of untried demand by a strict undercut.; reason: The source expected-utility consumers have identical posterior values for remaining untried goods at fixed history; the assumptions are local demand properties, not zero-profit conditions.
--   - reading: In any equilibrium. → In any equilibrium of the terminal segment game, without assumptions about unrelated period-2 demand.; reason: Only terminal Bertrand deviations enter the source argument.
--   - encoding: k,l differ from i, with outside history l=0 allowed. → k ≠ i and l ≠ some i, with l=none allowed.; reason: Four firms ensure an untried rival even after two distinct trials; prior offers are fixed for terminal deviations.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 52 (PDF 54), Lemma D.2

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod

namespace SpilloverDuopoly.Switchers.Supplement

/-- Lemma D.2 (p. 52 (PDF 54)): if neither of the segment's earlier purchases `k`, `l` is firm
`i`'s product (`l = none`, the outside option, included), then in any equilibrium of that segment's
third-period game `π_i^{kl} = 0`. -/
theorem lemma_D2 (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (k : Fin 4) (l : Option (Fin 4))
    (hD : UntriedSubstitutes (ThreePeriod.untried3 k l) (G.demand3 k (o2 k) l))
    (heq : G.IsTermEq k (o2 k) l (o3 k (o2 k) l)) (i : Fin 4) (hk : k ≠ i) (hl : l ≠ some i) :
    G.piKL o2 o3 i k l = 0 := by sorry

end SpilloverDuopoly.Switchers.Supplement
