-- Prove2me | Theorems.Thm_SlottingFees_proposition_3
-- name    : SlottingFees.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:41.113287+00:00
-- url     : https://prove2.me/theorems/09940259-cc32-4300-9b41-33ee105be41c
-- title:
--   Proposition 3 — the full equilibrium on $\Omega$: variety, fee (19), assortment and profit (20)
-- statement:
--   The five sets $\Omega^0_{\{1\}},\Omega^+_{\{1\}},\Omega^0_{\{2\}},\Omega^+_{\{2\}},\Omega^+_{\{1,2\}}$ are mutually exclusive and exhaustive subsets of $\Omega$. For every $\omega\in\Omega$ a subgame-perfect equilibrium of the main model exists, and in every one:
--
--   1. $|A^*|=1$ on $\Omega^0_{\{1\}}\cup\Omega^+_{\{1\}}\cup\Omega^0_{\{2\}}\cup\Omega^+_{\{2\}}$ and $|A^*|=2$ on $\Omega^+_{\{1,2\}}$;
--   2. the slotting fee is
--   $$
--   S^*=\begin{cases}0 & \omega\in\Omega^0_{\{1\}}\cup\Omega^0_{\{2\}},\\ v_1/8&\omega\in\Omega^+_{\{1\}},\\ v_2/8 & \omega\in\Omega^+_{\{2\}},\\ \dfrac{\min\{((2q_1-q_2)\sqrt{q_1v_1}-q_1\sqrt{q_2v_2})^2,((2q_1-q_2)\sqrt{q_1v_2}-q_1\sqrt{q_2v_1})^2\}}{2(q_1-q_2)(4q_1-q_2)^2} & \omega\in\Omega^+_{\{1,2\}};\end{cases}\qquad(19)
--   $$
--   3. the assortment is $A^*=\{1\}$ on $\Omega^0_{\{1\}}\cup\Omega^+_{\{1\}}$, $A^*=\{2\}$ on $\Omega^0_{\{2\}}\cup\Omega^+_{\{2\}}$, and $A^*=\{1,2\}$ on $\Omega^+_{\{1,2\}}$;
--   4. the retailer's profit is
--   $$
--   \Pi^*_r=\begin{cases}v_2/4-K & \omega\in\Omega^0_{\{1\}},\\ v_1/16+S^*-K&\omega\in\Omega^+_{\{1\}},\\ v_1/4-K&\omega\in\Omega^0_{\{2\}},\\ v_2/16+S^*-K&\omega\in\Omega^+_{\{2\}},\\ v_{12}+2S^*-2K&\omega\in\Omega^+_{\{1,2\}}.\end{cases}\qquad(20)
--   $$
--
--   High product variety arises only when $K$ is small and the two products are comparably attractive; under low variety the retailer charges a fee only when one product is significantly more attractive.
--
--   Differences from the source:
--   - reading: the sets Ω^k_A, defined in the proof of Proposition 3 in the online supplement (not in the source artifact) → Ω^+_{1,2} = {ω ∈ Ω : K < v12 + 2S^{|2|} − L(ω)} with L(ω) = max{3v1/16, v2/4} if r ≥ 1/2, else max{v1/4, 3v2/16}; the rest of Ω split by r ∈ [1/2,4/7], (4/7,1], [3/7,1/2), [0,3/7); reason: reconstructed from Propositions 1-2; agrees with every printed clause of Propositions 3 and 5 and with Corollary 2
--   - reading: the retailer selects the product variety that maximizes its profit (§4.3, p.16); ties unspecified → |A| = 2 iff Π^{|2|}_r > Π^{|1|}_r; on a tie |A| = 1; reason: the low-variety regions of Propositions 4-5 and Corollary 2 are the closed sets K ≥ …
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - reading: the retailer solves max over 0 ≤ S ≤ v_i/8 of Π̃_r(S) (p.12); when two fees are optimal, unspecified → the fee maximizes the retailer's profit over the fees at which the category is offered; the lowest maximizer is taken; reason: [0, v_i/8] is exactly the set of fees at which some manufacturer participates (Lemma 2); (10) prints S = 0 at r ∈ {3/7, 4/7}, where S = 0 and S = v_i/8 are both optimal
--   - reading: (w̃1, w̃2) solves (13) → a pure Nash equilibrium of (13) on w_l ≥ c_l in which each manufacturer takes its lowest best response; reason: best responses are unique when both demands are positive, so the selection only acts when a product has zero demand, where the rival at cost is the paper's 'price pressure' (p.16)
--   - encoding: the subgame equilibrium solved by backward induction (its outcome is 'the' equilibrium) → a subgame profile (retailer pricing after every wholesale price, stage-2 outcome after every fee, fee); the theorem asserts that such an equilibrium exists and that every one has the stated outcome; reason: subgame perfection made explicit; existence rules out a vacuous 'every equilibrium' statement
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 3, (19)–(20), p.17

import Mathlib
import Definitions.Def_SlottingFees_Game
import Definitions.Def_SlottingFees_Regions

namespace SlottingFees

/-- **Proposition 3**, p.17 (Alan, Kurtuluş, Nakkas, MSOM 2024, doi:10.1287/msom.2022.0143): the
full equilibrium on Ω.

The five sets `Ω^0_{{1}}, Ω^+_{{1}}, Ω^0_{{2}}, Ω^+_{{2}}, Ω^+_{{1,2}}` are mutually exclusive
and exhaustive subsets of Ω. For every `ω ∈ Ω` a subgame-perfect equilibrium exists, and in every
one:

* on `Ω^0_{{1}}`: `|A*| = 1`, `A* = {1}`, `S* = 0`, `Π*_r = v₂/4 − K`;
* on `Ω^+_{{1}}`: `|A*| = 1`, `A* = {1}`, `S* = v₁/8`, `Π*_r = v₁/16 + S* − K`;
* on `Ω^0_{{2}}`: `|A*| = 1`, `A* = {2}`, `S* = 0`, `Π*_r = v₁/4 − K`;
* on `Ω^+_{{2}}`: `|A*| = 1`, `A* = {2}`, `S* = v₂/8`, `Π*_r = v₂/16 + S* − K`;
* on `Ω^+_{{1,2}}`: `|A*| = 2`, `A* = {1,2}`,
  `S* = min{((2q₁−q₂)√(q₁v₁) − q₁√(q₂v₂))², ((2q₁−q₂)√(q₁v₂) − q₁√(q₂v₁))²}/(2(q₁−q₂)(4q₁−q₂)²)`,
  `Π*_r = v₁₂ + 2S* − 2K`.

**Formalization Note** The sets `Ω^k_A` are a reconstruction (see `OmegaPlus12`): their
definitions are in the online supplement, which the source artifact does not contain.
Products 1, 2 are `0`, `1`. -/
theorem proposition_3 :
    (Omega0_1 ∪ OmegaPlus_1 ∪ Omega0_2 ∪ OmegaPlus_2 ∪ OmegaPlus12 = Omega) ∧
    Pairwise (fun a b : Fin 5 =>
      Disjoint (![Omega0_1, OmegaPlus_1, Omega0_2, OmegaPlus_2, OmegaPlus12] a)
        (![Omega0_1, OmegaPlus_1, Omega0_2, OmegaPlus_2, OmegaPlus12] b)) ∧
    ∀ ω ∈ Omega, (∃ P : Profile, IsSPE true ω P) ∧
      ∀ P : Profile, IsSPE true ω P →
        (ω ∈ Omega0_1 → (P.assortment ω).card = 1 ∧ P.assortment ω = {0} ∧
          P.fee ω = 0 ∧ P.profit ω = ω.v 1 / 4 - ω.K) ∧
        (ω ∈ OmegaPlus_1 → (P.assortment ω).card = 1 ∧ P.assortment ω = {0} ∧
          P.fee ω = ω.v 0 / 8 ∧ P.profit ω = ω.v 0 / 16 + P.fee ω - ω.K) ∧
        (ω ∈ Omega0_2 → (P.assortment ω).card = 1 ∧ P.assortment ω = {1} ∧
          P.fee ω = 0 ∧ P.profit ω = ω.v 0 / 4 - ω.K) ∧
        (ω ∈ OmegaPlus_2 → (P.assortment ω).card = 1 ∧ P.assortment ω = {1} ∧
          P.fee ω = ω.v 1 / 8 ∧ P.profit ω = ω.v 1 / 16 + P.fee ω - ω.K) ∧
        (ω ∈ OmegaPlus12 → (P.assortment ω).card = 2 ∧ P.assortment ω = Finset.univ ∧
          P.fee ω = ω.S2min ∧ P.profit ω = ω.v12 + 2 * P.fee ω - 2 * ω.K) := by sorry

end SlottingFees
