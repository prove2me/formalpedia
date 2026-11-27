-- Prove2me | Theorems.Thm_SpilloverDuopoly_Switchers_Supplement_lemma_D1
-- name    : SpilloverDuopoly.Switchers.Supplement.lemma_D1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T22:39:37.338584+00:00
-- url     : https://prove2.me/theorems/e91bcd3c-fbd4-47e3-9190-7917eebe0bca
-- title:
--   Lemma D.1, p. 52 (PDF 54) — third-period profits π_i^{kl} from every segment are nonnegative in equilibrium
-- statement:
--   Fix a period-2 offer profile and a terminal history $(k,l)$ in the four-firm three-period game, including $l=0$. In any equilibrium of that history's terminal pricing game every firm's selected-history profit satisfies
--   $$\pi_i^{kl}\ge0.$$
--   Quantities are per unit of initial share $\lambda_k$. The result applies even to zero-mass histories. It supplies terminal nonnegativity for Theorem D.2.
--
--   **Formalization Note** The theorem uses the segment game's Nash equilibrium alone; it requires no earlier-period equilibrium or demand-substitution hypothesis.
--
--   Differences from the source:
--   - generalization: Terminal segment demand from the source consumer-learning game. → Any real-valued segment-demand interface, with a terminal Nash equilibrium.; reason: Not selling has margin zero independently of demand, so the same argument includes every source instance and does not require earlier demand assumptions.
--   - reading: In any equilibrium. → In any equilibrium of the fixed terminal segment game.; reason: The source proof uses only a terminal no-sale deviation; whole-game equilibrium implies this local condition.
--   - encoding: Third-period history (k,l), including l=0. → Fin 4 firms, Option (Fin 4) second choices, and prices contingent on preceding offers; no sale is Option.none.; reason: Retain the outside history, zero mass, price-dependent selection and unrestricted real-price deviations.
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), p. 52 (PDF 54), Lemma D.1

import Mathlib
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_ThreePeriod

namespace SpilloverDuopoly.Switchers.Supplement

/-- Lemma D.1 (p. 52 (PDF 54)): in any equilibrium of the third-period pricing game of segment
`(k, l)`, every firm's third-period profit `π_i^{kl}` from that segment is nonnegative. -/
theorem lemma_D1 (G : ThreePeriod) (o2 : Fin 4 → Fin 4 → Offer)
    (o3 : Fin 4 → (Fin 4 → Offer) → Option (Fin 4) → Fin 4 → Offer) (k : Fin 4) (l : Option (Fin 4))
    (heq : G.IsTermEq k (o2 k) l (o3 k (o2 k) l)) (i : Fin 4) :
    0 ≤ G.piKL o2 o3 i k l := by sorry

end SpilloverDuopoly.Switchers.Supplement
