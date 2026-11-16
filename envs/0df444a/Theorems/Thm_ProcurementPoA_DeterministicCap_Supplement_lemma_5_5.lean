-- Prove2me | Theorems.Thm_ProcurementPoA_DeterministicCap_Supplement_lemma_5_5
-- name    : ProcurementPoA.DeterministicCap.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:50.375214+00:00
-- url     : https://prove2.me/theorems/6834a775-52b0-459d-a738-03a14bc1b0ff
-- title:
--   Lemma 5.5 — For every phantom mechanism and every c ∈ [1,R], PoA(M) ≥ 1 + (R − c)E_s[1 − σ_s(c)]/c (two-supplier instance: cost c and cost R).
-- statement:
--   Let $R\ge1$ and let $M$ be any phantom mechanism on any measurable public signal space with law $\rho$. Its conditional phantom law is a Markov kernel $\kappa$, supported at or below $R$ for almost every signal; $S_s(b)=\kappa(s,[b,\infty))$. For $c\in[1,R]$, let $\sigma_s(c)$ be the acceptance probability of the largest monopoly-profit-maximizing bid, with $\sigma_s(c)=0$ when monopoly profit is zero. Then
--   $$\operatorname{PoA}(M)\ge1+\frac{R-c}{c}\mathbb E_s[1-\sigma_s(c)].$$
--   No regularity assumption is imposed. This is the two-supplier rejection bound used in Theorem 5.7.
--
--   **Formalization Note** The expectation is a nonnegative Lebesgue integral. The map $s\mapsto\sigma_s(c)$ is measurable: kernel tail probabilities are measurable in $s$ for each bid, left continuity in the real bid gives a measurable monopoly value and largest-maximizer selection, and the zero-profit convention preserves measurability. No measurability certificate is assumed as a theorem hypothesis.
--
--   Differences from the source:
--   - generalization: the normalized nondegenerate cost interval → R ≥ 1, including R = 1; reason: at R = 1 the rejection term is zero and all outcome costs are 1
--   - encoding: public signals, conditional phantom bids, and signal-dependent mixed strategies → an arbitrary measurable signal space, a signal probability law and phantom Markov kernel, with strategy kernels jointly measurable in signal and cost; reason: implements Definition 5.1 and §5.2 without a finite-signal, density, or deterministic-strategy restriction
--   - encoding: PoA and the ordinary expectation of rejection probabilities → a complete-lattice nonnegative extended-real PoA and nonnegative Lebesgue expectation; reason: the rejection integrand is measurable and bounded by 1; the normalized optimum is positive
-- source:
--   Simone Palazzotto, Andrés Cristi, At What Cost? (In)efficiency in First-Price Procurement Auctions, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, Lemma 5.5, printed p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Supplement_Mechanism

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology Classical

namespace ProcurementPoA.DeterministicCap.Supplement

universe u

/-- No regularity assumption: this is the rejection bound for every phantom mechanism. -/
theorem lemma_5_5 (R : ℝ) (hR : 1 ≤ R) {Sig : Type u} [MeasurableSpace Sig]
    (M : PhantomMechanism R Sig) (c : ℝ) (hc : c ∈ Set.Icc 1 R) :
    ENNReal.ofReal 1 + ENNReal.ofReal ((R - c) / c) *
      (∫⁻ s, ENNReal.ofReal (1 - sigma R (signalAcceptance M s) c) ∂M.signalLaw) ≤
    mechanismPoA M := by sorry

end ProcurementPoA.DeterministicCap.Supplement
