-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_2_6
-- name    : SpatialHalfspace.FullLabels.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:28:41.917805+00:00
-- url     : https://prove2.me/theorems/2b647ad7-6b1c-4e33-8299-019745223aa2
-- title:
--   Lemma 2.6 — Transcript entropy
-- statement:
--   Let $\Pi$ be a legal protocol on a substrate $G$, driven by inputs $X$ and tapes $R$ (independent, $R$ with the protocol's tape law), and let $\Xi,\Psi$ be arbitrary random variables on the same probability space. For $W\subseteq V$, let $T_{\partial W}=(T_f)_{f\in\partial_G W}$ and $C_W=\sum_{f\in\partial_G W}\mathbb E|T_f|$. Then
--
--   $$I(\Psi;T_{\partial W}\mid \Xi,R)\ \le\ C_W .$$
--
--   Information about anything that crosses a cut is bounded by the expected number of bits on the cut, because for each fixed $R$ the transcripts on an edge form a prefix-free code.
--
--   Differences from the source:
--
--   - encoding: R, the random tapes of the protocol, independent of the inputs; C_W → a random variable R with the protocol’s tape law, independent of the input vector X; C_W computed under the law of X times the tape law; reason: this is the probability model of Definitions 2.2–2.3
--   - encoding: Shannon information in bits of arbitrary random variables → conditional mutual information from finite measurable quantizations, in [0, ∞], for measurable Ξ, Ψ, X, R and measurable transcripts; reason: this is Shannon conditional information; the countable transcript tuple is fully captured by its finite measurable quantizations
--   - encoding: an informal binary interactive protocol with shared and private tapes → the round model of the Protocol definition: one bit or nothing per direction per edge per round, local latched halting, a finite timed receive history at halting, local finalization that may discard unused receive or timing information, root output from its own input, tapes and final local state, prefix-freeness and cut replay, and almost-sure finite halting at every vertex; reason: finite local halting implements the source’s termination requirement; arbitrary delays and computation are uncharged, messages can be serialized into rounds, and cut replay of final states excludes uncharged timing or control information from affecting the output while allowing unused information to be discarded
--   - generalization: positive physical dimension and a nonempty terminal population → any natural physical dimension and finite terminal set, including zero dimension and empty terminals; reason: the prefix-code entropy bound does not use positive dimension or terminal count; all source substrates are included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 7, PDF p. 8, Lemma 2.6, PDF p. 8

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 2.6 (Transcript entropy), printed p. 7. For a legal protocol driven by inputs `X`
and tapes `R` (independent, `R` with the protocol's tape law), arbitrary random variables `Ξ, Ψ`
and any vertex set `W`: `I(Ψ; T_{∂W} | Ξ, R) ≤ C_W = ∑_{f ∈ ∂W} E|T_f|` (bits). -/
theorem lemma_2_6 {p : ℕ} {U : Type} [Fintype U] {S : Substrate p U} {Inp Out : Type}
    [MeasurableSpace Inp] (Pr : Protocol S Inp Out) {Ω β γ : Type} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (U → Inp)) (R : Ω → Pr.Tape) (Ξ : Ω → β) (Ψ : Ω → γ)
    (hX : Measurable X) (hR : Measurable R) (hΞ : Measurable Ξ) (hΨ : Measurable Ψ)
    (hindep : IndepFun X R μ) (hRlaw : μ.map R = Pr.tapeLaw)
    (hlegal : Pr.Legal (μ.map X)) (hmeas : Pr.MeasurableTranscripts) (W : Set (Fin S.N)) :
    condMutualInfoBits Ψ (fun ω (e : S.boundary W) => Pr.transcript (X ω) (R ω) e)
        (fun ω => (Ξ ω, R ω)) μ ≤ Pr.cutTraffic (μ.map X) W := by sorry

end SpatialHalfspace.FullLabels
