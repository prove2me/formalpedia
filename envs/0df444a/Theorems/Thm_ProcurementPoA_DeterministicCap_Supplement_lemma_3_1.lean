-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_3_1
-- name    : ProcurementPoA.DeterministicCap.Supplement.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:30.142627+00:00
-- url     : https://prove2.me/theorems/f4640570-9816-4273-bfeb-a28ae238254e
-- title:
--   Lemma 3.1 — With N ≥ 2 deterministic costs, the standard (uncapped, unrestricted-bid) auction has a sequence of mixed equilibria whose social cost
-- statement:
--   Fix $N=n+1\ge2$ suppliers with arbitrary deterministic real costs $c_i$, and any measurable lowest-bid tie rule $\tau$. In the standard first-price procurement auction, bids and deviations range over all real numbers. There exists a sequence of mixed no-underbidding Nash equilibria $\sigma^k$ such that
--   $$\mathrm{SC}(\sigma^k)=\sum_i c_i\Pr_{\sigma^k}(i\text{ wins})\longrightarrow\frac1N\sum_i c_i.$$
--   Writing $c_{\min}=\min_i c_i$, if $c_{\min}>0$, the supremum of the ratios of equilibria for this same deterministic instance and tie rule satisfies
--   $$\operatorname{PoA}(c,\tau)\ge\frac{\frac1N\sum_i c_i}{c_{\min}}.$$
--   This supplies the mixed-equilibrium sequence behind both parts of Theorem 3.3. Negative or coincident costs are allowed in the convergence clause; only the ratio clause uses positivity.
--
--   Differences from the source:
--   - encoding: independent private costs, mixed used bids and arbitrary tie rules → Fin (n+1) suppliers, Borel type laws, Markov bid and tie kernels, and typewise incentives almost everywhere in the drawn bid; reason: covers every nonempty finite population and cost atoms using the published model; used bids are interpreted probabilistically rather than as topological support endpoints
--   - encoding: SC tends to the arithmetic mean for arbitrary deterministic real costs → SC is a finite signed sum of costs times real winning probabilities, and convergence is along natural sequence indices; reason: preserves negative costs without truncation and makes the displayed sequential limit explicit
--   - encoding: the consequent divides by the minimum cost → the consequent is conditional on a strictly positive minimum cost; reason: the paper uses this ratio for positive procurement costs in Theorem 3.3; the arbitrary-real convergence clause is unchanged
--   - generalization: PoA is the supremum over the auction class and all tie rules → the consequent already holds for the fixed deterministic instance and each tie rule; reason: the construction works for every tie rule and this instance supremum is bounded by the source class supremum
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma 3.1, printed p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_StandardAuction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

/-- Lemma 3.1: every tie rule; arbitrary real deterministic costs. -/
theorem lemma_3_1 {n : ℕ} (hn : 1 ≤ n) (c : Suppliers n → ℝ) (τ : TieRule n) :
    (∃ σ : ℕ → MixedProfile n,
      (∀ k, IsStandardBNE (deterministicTypes c) τ (σ k)) ∧
      Tendsto (fun k => deterministicSocialCost c τ (σ k)) atTop
        (𝓝 ((∑ i, c i) / (n + 1 : ℕ)))) ∧
    (0 < lowest c → ENNReal.ofReal (((∑ i, c i) / (n + 1 : ℕ)) / lowest c) ≤
      standardInstancePoA (deterministicTypes c) τ) := by sorry

end ProcurementPoA.DeterministicCap.Supplement
