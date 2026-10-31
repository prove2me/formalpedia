-- Prove2me | Theorems.Thm_SlottingFees_proposition_4
-- name    : SlottingFees.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:34.524025+00:00
-- url     : https://prove2.me/theorems/09687af6-4365-4dde-80f8-201aae315c7f
-- title:
--   Proposition 4 — the benchmark without slotting fees: assortment $\bar A$ and profit (21)
-- statement:
--   In the benchmark model, where the retailer sets the slotting fee to zero in the first stage, for every $\omega\in\Omega$ a subgame-perfect equilibrium exists, and in every one the retailer sets $\bar A=\{1\}$ on $\bar\Omega_{\{1\}}$, $\bar A=\{2\}$ on $\bar\Omega_{\{2\}}$ and $\bar A=\{1,2\}$ on $\bar\Omega_{\{1,2\}}$, with profit
--   $$
--   \bar\Pi_r=\begin{cases}\max\{v_1/16,\ v_2/4\}-K & \omega\in\bar\Omega_{\{1\}},\\ \max\{v_1/4,\ v_2/16\}-K&\omega\in\bar\Omega_{\{2\}},\\ v_{12}-2K & \omega\in\bar\Omega_{\{1,2\}}.\end{cases}\qquad(21)
--   $$
--
--   Comparing this with Proposition 3 isolates the effect of slotting fees on the assortment.
--
--   Differences from the source:
--   - reading: benchmark: 'a special case of our main model in which the retailer sets the slotting fee to zero in the first stage' (p.20) → the same game with the fee fixed at 0 in both subgames, with the same tie rules; reason: the literal reading of p.20
--   - reading: the retailer selects the product variety that maximizes its profit (§4.3, p.16); ties unspecified → |A| = 2 iff Π^{|2|}_r > Π^{|1|}_r; on a tie |A| = 1; reason: the low-variety regions of Propositions 4-5 and Corollary 2 are the closed sets K ≥ …
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - reading: (w̃1, w̃2) solves (13) → a pure Nash equilibrium of (13) on w_l ≥ c_l in which each manufacturer takes its lowest best response; reason: best responses are unique when both demands are positive, so the selection only acts when a product has zero demand, where the rival at cost is the paper's 'price pressure' (p.16)
--   - encoding: the subgame equilibrium solved by backward induction (its outcome is 'the' equilibrium) → a subgame profile (retailer pricing after every wholesale price, stage-2 outcome after every fee, fee); the theorem asserts that such an equilibrium exists and that every one has the stated outcome; reason: subgame perfection made explicit; existence rules out a vacuous 'every equilibrium' statement
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 4, (21), p.20

import Mathlib
import Definitions.Def_SlottingFees_Game
import Definitions.Def_SlottingFees_Regions

namespace SlottingFees

/-- **Proposition 4**, p.20 (Alan, Kurtuluş, Nakkas, MSOM 2024, doi:10.1287/msom.2022.0143): the
benchmark model without slotting fees.

For every `ω ∈ Ω` a subgame-perfect equilibrium of the benchmark exists (the game with the
slotting fee fixed at zero in the first stage, §5.2, p.20), and in every one the retailer sets
`Ā = {1}` on `Ω̄_{{1}}`, `Ā = {2}` on `Ω̄_{{2}}`, `Ā = {1,2}` on `Ω̄_{{1,2}}`, with profit (21):
`Π̄_r = max{v₁/16, v₂/4} − K`, `max{v₁/4, v₂/16} − K`, `v₁₂ − 2K` respectively.

**Formalization Note** Products 1, 2 are `0`, `1`. -/
theorem proposition_4 :
    ∀ ω ∈ Omega, (∃ P : Profile, IsSPE false ω P) ∧
      ∀ P : Profile, IsSPE false ω P →
        (ω ∈ OmegaBar1 → P.assortment ω = {0} ∧
          P.profit ω = max (ω.v 0 / 16) (ω.v 1 / 4) - ω.K) ∧
        (ω ∈ OmegaBar2 → P.assortment ω = {1} ∧
          P.profit ω = max (ω.v 0 / 4) (ω.v 1 / 16) - ω.K) ∧
        (ω ∈ OmegaBar12 → P.assortment ω = Finset.univ ∧
          P.profit ω = ω.v12 - 2 * ω.K) := by sorry

end SlottingFees
