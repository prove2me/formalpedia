-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_reverse_extraction_shaper
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.reverse_extraction_shaper
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:52:42.816229+00:00
-- url     : https://prove2.me/theorems/0e1f7b22-235e-475b-81c9-fcd708c60db4
-- title:
--   Reverse extraction reproduces the source distribution and cq correlations
-- statement:
--   Let $P_X$ be a law on $X$ and $f:X\to U$ a deterministic extractor with induced law $q(u)=\sum_{x:f(x)=u}P_X(x)$. Assume $\varepsilon\ge0$ and $\tfrac12\sum_u|q(u)-|U|^{-1}|\le\varepsilon$. There is a stochastic shaper $S(x|u)$, using private randomness, with $S(x|u)=P_X(x)/q(u)$ when $f(x)=u$ and $q(u)>0$, zero for other $x$ at such $u$, and an arbitrary normalized conditional law at zero-mass $u$, such that
--
--   $$
--   \sum_u q(u)S(x|u)=P_X(x),\qquad
--   \frac12\sum_x\left|\sum_u\frac{S(x|u)}{|U|}-P_X(x)\right|\le\varepsilon.
--   $$
--
--   For every cq eavesdropper channel $x\mapsto\rho_Z^x$, the complete joint state of the actual input $U'$ with law $q$ and the shaper's output through that channel equals the extractor-output/eavesdropper state before reversal. Consequently every trace-distance privacy-amplification bound relative to a uniform $U$ and a fixed normalized reference $\sigma_Z$ holds unchanged for that actual-input joint state. This identity explains how reverse extraction preserves secrecy while reproducing the desired source law.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   For uniform shaper input, the joint input/eavesdropper trace distance to the same uniform-product reference is at most $\delta+\varepsilon$ whenever the original extracted state has distance at most $\delta$. In particular an $\varepsilon$-private extractor yields uniform-input secrecy error at most $2\varepsilon$, as used in section II.D.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 4, §II.C: reverse extraction constructs a distribution shaper

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P30

variable {X Y Z M U V A B C : Type*}

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z] [Fintype M] [DecidableEq M]

variable [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C]

attribute [local instance] Classical.propDecidable

/-- Section II.C, PDF p.4: reverse extraction samples P(X|U'=u) with private
randomness. At zero-mass u the normalized law can be arbitrary. Exact reproduction
uses the actual extracted law U'; uniform input is epsilon-close. The complete
cq identity preserves the actual-law privacy guarantee. With uniform input,
the secrecy error is at most delta + epsilon, hence 2 epsilon when delta=epsilon. -/
theorem reverse_extraction_shaper [Nonempty X] [Nonempty U] [Nonempty Z]
    (p : RRDistribution X) (extract : X → U) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hnear : tvDist (rrExtractedLaw p.prob extract) (rrUniform U) ≤ epsilon) :
    ∃ shape : U → RRDistribution X,
      (∀ u, rrExtractedLaw p.prob extract u ≠ 0 → ∀ x,
        (shape u).prob x =
          if extract x = u then p.prob x / rrExtractedLaw p.prob extract u else 0) ∧
      rrShapedLaw (rrExtractedLaw p.prob extract) shape = p.prob ∧
      tvDist (rrShapedLaw (rrUniform U) shape) p.prob ≤ epsilon ∧
      (∀ thetaZ : X → Matrix Z Z ℂ, RRIsCq thetaZ →
        rrCqState (rrExtractedLaw p.prob extract) (rrPreprocess thetaZ shape) =
          rrExtractedState p.prob extract thetaZ) ∧
      (∀ (thetaZ : X → Matrix Z Z ℂ) (reference : Matrix Z Z ℂ) (delta : ℝ),
        RRIsCq thetaZ → IsDensityMatrix reference → 0 ≤ delta →
        traceNorm (rrExtractedState p.prob extract thetaZ -
          rrUniformReference (U := U) reference) / 2 ≤ delta →
        (traceNorm (rrCqState (rrExtractedLaw p.prob extract) (rrPreprocess thetaZ shape) -
          rrUniformReference (U := U) reference) / 2 ≤ delta ∧
        traceNorm (rrCqState (rrUniform U) (rrPreprocess thetaZ shape) -
          rrUniformReference (U := U) reference) / 2 ≤ delta + epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
