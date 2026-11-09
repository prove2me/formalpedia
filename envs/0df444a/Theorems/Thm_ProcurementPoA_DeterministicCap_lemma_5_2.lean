-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_lemma_5_2
-- name    : ProcurementPoA.DeterministicCap.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:48.840224+00:00
-- url     : https://prove2.me/theorems/642ebfd5-b82f-43c9-8704-1d460cb2c0e7
-- title:
--   Lemma 5.2 — expected capped social-cost bound
-- statement:
--   Fix real numbers $R\ge1$ and $T\ge1$. Consider any nonempty finite supplier population, arbitrary independent Borel cost laws on $[1,R]$, any measurable lowest-bid tie rule, and any mixed Bayes–Nash equilibrium of $M_T$ in which suppliers do not bid below their own costs. With $C^\star=\min_i c_i$ and $\varepsilon=e^{-2}$,
--
--   $$\mathrm{SC}\le\mathbb E[g_{R,T}(C^\star)],\qquad g_{R,T}(c)=\begin{cases}c+\varepsilon(T-c),&c<T,\\R,&c\ge T.\end{cases}$$
--
--   The comparison is an unconditional expectation bound. It retains arbitrary cost atoms, real bids and independent mixed randomization. It supplies the sharp upper comparison needed by the deterministic-cap theorem; it does not assume a transformed-welfare guarantee or any tightness family.
--
--   Differences from the source:
--   - generalization: nondegenerate positive cost interval, normalized to [1,R] → R ≥ 1, including R = 1; reason: equal endpoints give constant cost and preserve every source instance
--   - generalization: Definition 5.1 restricts the phantom class to T ≤ R, while Lemma 5.2 prints T ≥ 1 → all real T ≥ 1, including T > R; reason: the same deterministic rule and expected comparison remain meaningful above R; no printed threshold is lost
--   - encoding: independent costs, mixed used bids, arbitrary ties and ordinary expectation → Borel type laws, Markov bid and tie kernels, typewise best responses almost everywhere in the drawn bid, and nonnegative extended-real expectation; reason: implements the probabilistic meaning of used bids including atoms; positive bounded costs give the same finite expectation, without topological-support or integrability defaults
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma 5.2, printed p. 9 (PDF p. 11); proof Appendix A.1.1, printed pp. 16–17 (PDF pp. 18–19)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction
import Definitions.Def_ProcurementPoA_DeterministicCap_CapFormula

open MeasureTheory

namespace ProcurementPoA.DeterministicCap

/-- Lemma 5.2, including the literal threshold domain T ≥ 1.
The rule is defined also for T > R, extending Definition 5.1's cap class. -/
theorem lemma_5_2 (R T : ℝ) (hR : 1 ≤ R) (hT : 1 ≤ T)
    {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n)
    (hcost : InCostInterval D 1 R) (heq : IsBNE D τ σ T) :
    socialCost D τ σ R T ≤ ∫⁻ c, ENNReal.ofReal (gCap R T (lowest c)) ∂(typeLaw D) := by sorry

end ProcurementPoA.DeterministicCap
