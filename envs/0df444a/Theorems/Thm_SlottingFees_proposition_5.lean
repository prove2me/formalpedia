-- Prove2me | Theorems.Thm_SlottingFees_proposition_5
-- name    : SlottingFees.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:06.58323+00:00
-- url     : https://prove2.me/theorems/5ddf4c05-aac0-4671-8a95-c13017b7ff88
-- title:
--   Proposition 5 — slotting fees raise, lower or keep product variety on $\Phi_\uparrow$, $\Phi_\downarrow$, $\Phi_0$ (corrected: $\Phi_\uparrow$ second set)
-- statement:
--   Let $\omega\in\Omega$. Equilibria exist both in the main model (with slotting fees) and in the benchmark (slotting fee fixed at zero), and:
--
--   1. **Category expansion.** If $\omega\in\Phi_\uparrow$, every equilibrium assortment of the benchmark is $\bar A=\{1\}$ or $\bar A=\{2\}$, and every equilibrium assortment of the main model is $A^*=\{1,2\}$.
--   2. **Competitive exclusion.** If $\omega\in\Phi_\downarrow$, every equilibrium assortment of the benchmark is $\bar A=\{1,2\}$, and every equilibrium assortment of the main model is $A^*=\{1\}$ or $A^*=\{2\}$.
--   3. **Rent extraction.** If $\omega\in\Phi_0=\Omega\setminus(\Phi_\downarrow\cup\Phi_\uparrow)$, the two models have the same equilibrium assortment,
--   $$
--   A^*=\bar A\in\bigl\{\{1\},\ \{2\},\ \{1,2\}\bigr\}.
--   $$
--
--   Here
--   $$
--   \Phi_\uparrow=\{\omega\in\Omega: v_1\ge v_2,\ v_{12}-\max\{\tfrac{v_1}{16},\tfrac{v_2}{4}\}\le K<v_{12}+2S^{|2|}-\max\{\tfrac{3v_1}{16},\tfrac{v_2}{4}\}\}\cup\{\omega\in\Omega: v_1<v_2,\ v_{12}-\max\{\tfrac{v_1}{4},\tfrac{v_2}{16}\}\le K<v_{12}+2S^{|2|}-\max\{\tfrac{v_1}{4},\tfrac{3v_2}{16}\}\}
--   $$
--   and
--   $$
--   \Phi_\downarrow=\{\omega\in\Omega: v_1\ge v_2,\ v_{12}+2S^{|2|}-\tfrac{3v_1}{16}\le K<v_{12}-\max\{\tfrac{v_1}{16},\tfrac{v_2}{4}\}\}\cup\{\omega\in\Omega: v_1<v_2,\ v_{12}+2S^{|2|}-\tfrac{3v_2}{16}\le K<v_{12}-\max\{\tfrac{v_1}{4},\tfrac{v_2}{16}\}\}.
--   $$
--
--   Slotting fees can thus both widen and narrow the retailer's assortment; on $\Phi_0$ they only transfer surplus from the manufacturers to the retailer.
--
--   Differences from the source:
--   - correction: Φ↑, second set, lower bound v12 − max{v1/16, v2/4} ≤ K → v12 − max{v1/4, v2/16} ≤ K; reason: the printed bound is the v1 ≥ v2 one; at (q1, q2, c1, c2, K) = (1.1, 1, 0.13, 0, 0) ∈ Ω the printed condition holds but the benchmark's high-variety profit v12 ≈ 0.2182 exceeds its low-variety profit max{v1/4, v2/16} ≈ 0.2138, so Ā = {1,2}; the mirrored bound matches Proposition 4's Ω̄_{2}
--   - reading: Φ0 ≡ Ω \ (Ω↓ ∪ Ω↑) → Ω \ (Φ↓ ∪ Φ↑); reason: Ω↓ and Ω↑ are defined nowhere; the sets of parts (a), (b) are Φ↑, Φ↓, and p.21 calls the set of (c) Φ0
--   - reading: the retailer selects the product variety that maximizes its profit (§4.3, p.16); ties unspecified → |A| = 2 iff Π^{|2|}_r > Π^{|1|}_r; on a tie |A| = 1; reason: the low-variety regions of Propositions 4-5 and Corollary 2 are the closed sets K ≥ …
--   - reading: benchmark: 'a special case of our main model in which the retailer sets the slotting fee to zero in the first stage' (p.20) → the same game with the fee fixed at 0 in both subgames, with the same tie rules; reason: the literal reading of p.20
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - reading: the retailer solves max over 0 ≤ S ≤ v_i/8 of Π̃_r(S) (p.12); when two fees are optimal, unspecified → the fee maximizes the retailer's profit over the fees at which the category is offered; the lowest maximizer is taken; reason: [0, v_i/8] is exactly the set of fees at which some manufacturer participates (Lemma 2); (10) prints S = 0 at r ∈ {3/7, 4/7}, where S = 0 and S = v_i/8 are both optimal
--   - reading: (w̃1, w̃2) solves (13) → a pure Nash equilibrium of (13) on w_l ≥ c_l in which each manufacturer takes its lowest best response; reason: best responses are unique when both demands are positive, so the selection only acts when a product has zero demand, where the rival at cost is the paper's 'price pressure' (p.16)
--   - encoding: 'the equilibrium assortment … is …' → equilibrium assortments are the path assortments of subgame-perfect equilibria; the theorem asserts that one exists and that every one is as stated; reason: the definite article presupposes an equilibrium; stating existence rules out a vacuous predicate
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 5, pp.20–21

import Mathlib
import Definitions.Def_SlottingFees_Game
import Definitions.Def_SlottingFees_Regions

namespace SlottingFees

/-- **Proposition 5**, pp.20–21 (Alan, Kurtuluş, Nakkas, *Retail Category Management with
Slotting Fees*, MSOM 2024, doi:10.1287/msom.2022.0143), part (a) corrected: the impact of
slotting fees on the equilibrium product variety and assortment composition.

For every `ω ∈ Ω`, equilibria exist both in the main model and in the benchmark, and

* (a) on `Φ↑` every benchmark equilibrium assortment is `{1}` or `{2}`, and every main-model
  equilibrium assortment is `{1, 2}`;
* (b) on `Φ↓` every benchmark equilibrium assortment is `{1, 2}`, and every main-model
  equilibrium assortment is `{1}` or `{2}`;
* (c) on `Φ0 = Ω \ (Φ↓ ∪ Φ↑)` the two models have the same equilibrium assortment, which is
  `{1}`, `{2}` or `{1, 2}`.

**Formalization Note** `Φ↑` is corrected in its second set (see `PhiUp`); `Φ0` reads the printed
`Ω↓, Ω↑` as `Φ↓, Φ↑` (see `PhiZero`). Equilibrium assortments are those on the path of a
subgame-perfect equilibrium (`IsEqAssortment`). Products 1, 2 are `0`, `1`. -/
theorem proposition_5 (ω : Params) (hω : ω ∈ Omega) :
    (∃ A, IsEqAssortment true ω A) ∧ (∃ A, IsEqAssortment false ω A) ∧
    (ω ∈ PhiUp →
      (∀ A, IsEqAssortment false ω A → A = {0} ∨ A = {1}) ∧
      (∀ A, IsEqAssortment true ω A → A = Finset.univ)) ∧
    (ω ∈ PhiDown →
      (∀ A, IsEqAssortment false ω A → A = Finset.univ) ∧
      (∀ A, IsEqAssortment true ω A → A = {0} ∨ A = {1})) ∧
    (ω ∈ PhiZero →
      ∀ A B, IsEqAssortment true ω A → IsEqAssortment false ω B →
        A = B ∧ (A = {0} ∨ A = {1} ∨ A = Finset.univ)) := by sorry

end SlottingFees
