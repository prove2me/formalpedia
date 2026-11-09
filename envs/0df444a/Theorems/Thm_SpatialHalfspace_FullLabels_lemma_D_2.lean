-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_D_2
-- name    : SpatialHalfspace.FullLabels.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:33.352195+00:00
-- url     : https://prove2.me/theorems/e62b082b-5325-4170-9f88-81b1bd88bb36
-- title:
--   Lemma D.2 — Terminal-bit recovery
-- statement:
--   Let $G$ be a $p$-dimensional substrate, $p\ge 1$, and let $\sigma=(\sigma_i)_{i=1}^m$ be independent uniform bits held at distinct terminals $u_1,\dots,u_m$, with all other inputs fixed. Suppose a legal protocol $\Pi$ produces root estimates $\hat\sigma\in\{0,1\}^m$ satisfying
--
--   $$\Pr\big[d_H(\sigma,\hat\sigma)\le m/8\big]\ \ge\ 2/3 .$$
--
--   Let $a_0=1-h_2(1/4)>0$. If $m\ge\max\{2^{p+1},6/a_0\}$, then
--
--   $$\mathrm{BM}_G(\Pi)\ \ge\ \frac{a_0}{24\cdot 2^{1/p}}\,m^{1+1/p}.$$
--
--   **Formalization Note** The input of $u_i$ is $\mathrm{enc}_i(\sigma_i)$ for an arbitrary map $\mathrm{enc}_i$ and every other terminal has a fixed input; probabilities and costs are over uniform $\sigma$ and the protocol's tapes.
--
--   Differences from the source:
--
--   - generalization: bits held at the terminals u_i → the input of u_i is enc_i(σ_i) for an arbitrary map enc_i; reason: holding the bit is the case of an injective enc_i; a less informative input cannot help the protocol
--   - encoding: root estimates σ̂ and Pr over the bits and the protocol randomness → the root output of type {0,1}^m, measurable in inputs and tapes; the law of uniform σ times the tape law; reason: the probability model of §2
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - encoding: real-valued costs → costs in [0, ∞] (ℝ≥0∞), nonterminating traffic has infinite length; reason: an infinite or empty infimum must not become 0
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 19, PDF p. 20, Lemma D.2, PDF pp. 20–21

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma D.2 (Terminal-bit recovery), printed p. 19. Let `σ = (σ_i)_{i=1}^m` be independent
uniform bits held at distinct terminals `u_1, …, u_m` (the input of `u_i` is a function of `σ_i`),
with all other inputs fixed. If a legal protocol produces root estimates `σ̂ ∈ {0,1}^m` with
`Pr[d_H(σ, σ̂) ≤ m/8] ≥ 2/3`, then for `m ≥ max{2^{p+1}, 6/a₀}`,
`BM_G(Π) ≥ a₀/(24·2^{1/p}) m^{1+1/p}`. -/
theorem lemma_D_2 {p : ℕ} (hp : 1 ≤ p) {U : Type} [Fintype U] (S : Substrate p U) {Inp : Type}
    [MeasurableSpace Inp] (m : ℕ) (term : Fin m → U) (hterm : Function.Injective term)
    (enc : Fin m → Bool → Inp) (x0 : U → Inp) (Pr : Protocol S Inp (Fin m → Bool))
    (hmeas : Pr.MeasurableTranscripts)
    (hout : Measurable fun xR : (U → Inp) × Pr.Tape => Pr.rootOutput xR.1 xR.2)
    (hlegal : Pr.Legal ((uniformOn Set.univ : Measure (Fin m → Bool)).map
      fun σ => Function.extend term (fun i => enc i (σ i)) x0))
    (hrec : ENNReal.ofReal (2 / 3) ≤ ((uniformOn Set.univ : Measure (Fin m → Bool)).prod Pr.tapeLaw)
      {σR | (hammingDist σR.1
        (Pr.rootOutput (Function.extend term (fun i => enc i (σR.1 i)) x0) σR.2) : ℝ) ≤ (m : ℝ) / 8})
    (hm1 : (2 : ℝ) ^ (p + 1) ≤ m) (hm2 : 6 / a0 ≤ m) :
    ENNReal.ofReal (a0 / (24 * 2 ^ (1 / (p : ℝ))) * (m : ℝ) ^ (1 + 1 / (p : ℝ))) ≤
      Pr.BM ((uniformOn Set.univ : Measure (Fin m → Bool)).map
        fun σ => Function.extend term (fun i => enc i (σ i)) x0) := by sorry

end SpatialHalfspace.FullLabels
