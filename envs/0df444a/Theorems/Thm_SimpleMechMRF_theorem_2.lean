-- Prove2me | Theorems.Thm_SimpleMechMRF_theorem_2
-- name    : SimpleMechMRF.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:22.660602+00:00
-- url     : https://prove2.me/theorems/5f243bc0-1b14-44ca-93ea-1a2feccfd10b
-- title:
--   Theorem 2, p.12 — additive buyer, MRF values: $(2e^{4\Delta}+\sqrt2)\,\mathrm{SRev}+8(e^{4\Delta}+1)\,\mathrm{BRev}\ge\mathrm{Rev}(D)$
-- statement:
--   Let the type distribution $D$ be represented by a Markov random field (any number $n$ of items, finite nonnegative alphabets, any hypergraph, any real vertex and hyperedge potentials) with maximum weighted degree $\Delta$. If the buyer's valuation is additive, then
--
--   $$
--   \big(2e^{4\Delta}+\sqrt2\big)\cdot\mathrm{SRev}+8\big(e^{4\Delta}+1\big)\cdot\mathrm{BRev}\;\ge\;\mathrm{Rev}(D),
--   $$
--
--   where $\mathrm{Rev}(D)$ is the optimal revenue over all randomized IC and IR mechanisms, $\mathrm{SRev}$ the optimal revenue from selling the items separately, and $\mathrm{BRev}$ the optimal revenue from selling the grand bundle.
--
--   Hence $\max\{\mathrm{SRev},\mathrm{BRev}\}$ is an $O(e^{4\Delta})$-approximation to the optimal revenue, uniformly in the number of items. For independent items ($\Delta=0$) this recovers a constant-factor approximation of the type proved by Babaioff, Immorlica, Lucier and Weinberg.
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: mechanism M = (π, p) with allocation probabilities π_i(t) → a sub-probability lottery σ over feasible bundles S ∈ I at each report, π_i(t) = Σ_{S∈I, i∈S} σ(t,S), utility E_{S∼σ(t')}[v(t,S)] − p(t'); reason: a randomized allocation of a constrained-additive buyer is a distribution over feasible bundles; for I = 2^[n] every π ∈ [0,1]^n arises; same mechanisms
--   - encoding: IC and IR (no misreport gains; nonnegative truthful utility) → IC and IR for true types and reports in the support T; reason: the standard finite-type model; types outside T have probability 0 and reports outside T are never needed
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
--   - encoding: BRev, the optimal revenue from selling the grand bundle → sup_{p∈ℝ} p · Pr[Σ_i t_i ≥ p]; reason: selling the grand bundle is posting one price for it; the buyer buys when the bundle's value is at least the price
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Theorem 2, p.12 (PDF 13); proof in Appendix C, pp.30–31 (PDF 31–32)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Theorem 2** (Cai & Oikonomou, *On Simple Mechanisms for Dependent Items*,
arXiv:2106.10814v2, p. 12, PDF 13). Let the type distribution `D` be represented by an MRF `G`
(any number `n` of items, any finite nonempty alphabets of nonnegative values, any hypergraph,
any real vertex and local hyperedge potentials), with maximum weighted degree `Δ`. If the
buyer's valuation is additive, then
`(2 e^{4Δ} + √2) · SRev + 8 (e^{4Δ} + 1) · BRev ≥ Rev(D)`,
where `Rev(D)` is the optimal revenue over all randomized IC and IR mechanisms.

**Formalization Note.** `SRev = Σᵢ sup_p p · Pr[tᵢ ≥ p]`, `BRev = sup_p p · Pr[Σᵢ tᵢ ≥ p]`,
`Rev(D) = optRev D (additiveSystem n)`, the supremum over lottery mechanisms on all bundles that
are IC and IR on the support. -/
theorem theorem_2 {n : ℕ} (G : MRF n) :
    optRev G.law (additiveSystem n) ≤
      (2 * Real.exp (4 * G.maxWeightedDegree) + Real.sqrt 2) * srev G.law +
        8 * (Real.exp (4 * G.maxWeightedDegree) + 1) * brev G.law := by sorry

end SimpleMechMRF
