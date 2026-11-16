-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_theorem_3_3
-- name    : ProcurementPoA.DeterministicCap.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:07.1512+00:00
-- url     : https://prove2.me/theorems/b0064aa0-0a83-44fa-9bf4-3d5d487702ed
-- title:
--   Theorem 3.3 — The standard first-price procurement auction (no cap, unrestricted bids) has unbounded PoA
-- statement:
--   For every real interval $0<L<U$, the standard first-price procurement auction, with no bid cap and no outside option, has exact price of anarchy
--   $$\operatorname{PoA}_{[L,U]}=U/L.$$
--   The supremum ranges over all nonempty finite populations, arbitrary independent Borel cost laws on $[L,U]$, all measurable lowest-bid tie rules and all mixed no-underbidding Bayes–Nash equilibria, with every real deviation tested.
--
--   Moreover, for every real $M$ there are $0<L<U$, such a bounded positive-cost instance, a tie rule and an equilibrium whose ratio satisfies
--   $$\mathrm{SC}/\mathrm{SC}_{\mathrm{OPT}}>M.$$
--   Thus the unrestricted auction has unbounded inefficiency even when each witnessing instance has finite positive bounded costs. Both the exact bounded-interval value and unboundedness are asserted.
--
--   Differences from the source:
--   - encoding: independent private costs, mixed used bids and arbitrary tie rules → Fin (n+1) suppliers, Borel type laws, Markov bid and tie kernels, and typewise incentives almost everywhere in the drawn bid; reason: covers every nonempty finite population and cost atoms using the published model; used bids are interpreted probabilistically rather than as topological support endpoints
--   - encoding: the largest equilibrium ratio and an unbounded PoA → a nonnegative extended-real supremum equal to ofReal(U/L), and for every real M an actual equilibrium witness exceeding ofReal(M); reason: retains equality and both clauses while avoiding real-supremum defaults; the positive bounded witness costs preclude division by zero or infinite-mean shortcuts
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Theorem 3.3, printed p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Both the exact bounded-interval value and unboundedness on positive bounded instances. -/
theorem theorem_3_3 :
    (∀ L U : ℝ, 0 < L → L < U → standardPoA L U = ENNReal.ofReal (U / L)) ∧
    (∀ M : ℝ, ∃ (L U : ℝ) (n : ℕ) (D : IndependentTypes n)
      (τ : TieRule n) (σ : MixedProfile n),
      0 < L ∧ L < U ∧ InCostInterval D L U ∧ IsStandardBNE D τ σ ∧
      ENNReal.ofReal M < standardSocialCost D τ σ / optimalSocialCost D) := by sorry

end ProcurementPoA.DeterministicCap.Supplement
