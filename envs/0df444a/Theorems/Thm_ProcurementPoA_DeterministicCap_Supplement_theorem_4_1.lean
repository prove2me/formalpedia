-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_theorem_4_1
-- name    : ProcurementPoA.DeterministicCap.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:59.891962+00:00
-- url     : https://prove2.me/theorems/35764db2-51ce-4759-9b48-33a01d1309ac
-- title:
--   Theorem 4.1 — With costs and bids restricted to [c̲, c̄], every BNE satisfies E[c^eq] ≤ (1 − e^{-2})E[c⋆] + c̄e^{-2}, hence PoA ≤ 1 + e^{-2}(c̄/E[c⋆]
-- statement:
--   Let $0<L\le U$, and consider any nonempty finite supplier population with independent Borel cost laws on $[L,U]$. Fix any measurable lowest-bid tie rule and any mixed no-underbidding Bayes–Nash equilibrium whose used bids and allowed deviations lie in $[L,U]$. Every lowest bid is accepted; there is no outside option. Write $C^\star=\min_i c_i$, $\mathrm{SC}=\mathbb E[c^{\mathrm{eq}}]$, $\mathrm{SC}_{\mathrm{OPT}}=\mathbb E[C^\star]$ and $\varepsilon=e^{-2}$. Then
--   $$\mathrm{SC}\le(1-\varepsilon)\mathrm{SC}_{\mathrm{OPT}}+\varepsilon U,$$
--   and both ratio bounds hold:
--   $$\frac{\mathrm{SC}}{\mathrm{SC}_{\mathrm{OPT}}}\le1+\varepsilon\left(\frac{U}{\mathbb E[C^\star]}-1\right)\le1+\varepsilon\left(\frac UL-1\right).$$
--   This is the sharp-constant expectation guarantee for restricted bids. The Jin–Lu value-auction welfare theorem needed for its proof is a proof obligation, not an assumption of this statement.
--
--   Differences from the source:
--   - encoding: independent private costs, mixed used bids and arbitrary tie rules → Fin (n+1) suppliers, Borel type laws, Markov bid and tie kernels, and typewise incentives almost everywhere in the drawn bid; reason: covers every nonempty finite population and cost atoms using the published model; used bids are interpreted probabilistically rather than as topological support endpoints
--   - generalization: the nondegenerate positive interval used in §4 → 0 < L ≤ U including equal endpoints; reason: at equal endpoints all costs and allowed bids are the same and all three bounds are equalities; every source instance remains included
--   - encoding: ordinary expectations and division by expected optimal cost → nonnegative extended-real expectations and ratio, with the finite optimal cost converted to a real in the displayed comparison; reason: bounded positive costs ensure a finite strictly positive optimum, so these are the same three inequalities
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Theorem 4.1, printed p. 6 (PDF p. 8)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- The exact e^(-2) cost bound and both ratio inequalities. -/
theorem theorem_4_1 (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D L U) (heq : IsBidSetBNE D τ σ (Set.Icc L U)) :
    standardSocialCost D τ σ ≤
      ENNReal.ofReal (1 - epsilon) * optimalSocialCost D + ENNReal.ofReal (epsilon * U) ∧
    standardSocialCost D τ σ / optimalSocialCost D ≤
      ENNReal.ofReal (1 + epsilon * (U / (optimalSocialCost D).toReal - 1)) ∧
    1 + epsilon * (U / (optimalSocialCost D).toReal - 1) ≤
      1 + epsilon * (U / L - 1) := by sorry

end ProcurementPoA.DeterministicCap.Supplement
