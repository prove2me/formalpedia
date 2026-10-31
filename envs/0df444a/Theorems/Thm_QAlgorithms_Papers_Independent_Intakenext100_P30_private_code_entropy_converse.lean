-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_private_code_entropy_converse
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.private_code_entropy_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:53:31.604809+00:00
-- url     : https://prove2.me/theorems/452b0ae1-ada6-43f8-b1a1-3139d9e0a253
-- title:
--   Actual private-code errors imply smooth entropy bounds and a code converse
-- statement:
--   Let a stochastic code on $M$ have decoding error at most $\varepsilon$ for every message and eavesdropper trace distance at most $\varepsilon$ for every message to one fixed normalized reference. Assume $\varepsilon\ge0$ and put $r=\sqrt{2\varepsilon}$ and $b=\log_2|M|$. Let $M'$ be the actual decoder output. Then
--
--   $$
--   H_{\max}^{r}(M|M')\le0\quad\text{for every message law},\qquad
--   H_{\min}^{r}(M|Z)\ge b\quad\text{for uniform }M.
--   $$
--
--   For the uniform message law, the ensuing data-processing step also gives
--
--   $$
--   b\le H_{\min}^{r}(M|Z)-H_{\max}^{r}(M|Y).
--   $$
--
--   Both entropy inequalities and the code-level converse follow from the actual operational error conditions; none is a hypothesis. This supplies the source's common trace-error-to-purified-radius interface, rather than an assertion for two independent purified-distance error parameters.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
--
--   For a normalized cq state, smoothing ranges over positive subnormalized matrices at purified distance at most the indicated radius. Smooth min-entropy is an extended supremum and smooth max-entropy an extended infimum; at the zero operator their unsmoothed values are respectively $+\infty$ and $-\infty$.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 5, §III: private converse from actual code errors

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

/-- Section III, PDF p.5: both entropy inequalities are DERIVED from the actual
code's messagewise reliability and trace-distance secrecy. The max-entropy claim
holds for every message law, the min-entropy claim for the uniform law. The ensuing data-processing argument gives the
uniform-message code bound as well. This is the source's common sqrt(2 epsilon) interface, not an independent-(delta,epsilon)
purified-error statement. All nonnegative errors are included: radius >= 1
puts zero in the smoothing ball, giving Hmin=+infinity and Hmax=-infinity. -/
theorem private_code_entropy_converse [Nonempty X] [Nonempty Y] [Nonempty Z] [Nonempty M]
    (thetaY : X → Matrix Y Y ℂ) (thetaZ : X → Matrix Z Z ℂ)
    (hY : RRIsCq thetaY) (hZ : RRIsCq thetaZ) (code : RRCode M X Y)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon)
    (hgood : RRPrivateGood thetaY thetaZ code epsilon) :
    (∀ p : RRDistribution M,
      rrSmoothMax (rrCqState p.prob (fun m => Matrix.diagonal
        (fun guess => ((effectProb (code.decoder guess)
          (rrEncoded thetaY code.encoder m)) : ℂ)))) (Real.sqrt (2 * epsilon)) ≤ 0) ∧
    (Real.logb 2 (Fintype.card M : ℝ) : EReal) ≤
      rrSmoothMin (rrCqState (rrUniform M) (rrEncoded thetaZ code.encoder))
        (Real.sqrt (2 * epsilon)) ∧
    (Real.logb 2 (Fintype.card M : ℝ) : EReal) ≤
      rrSmoothMin (rrCqState (rrUniform M) (rrEncoded thetaZ code.encoder))
          (Real.sqrt (2 * epsilon)) -
        rrSmoothMax (rrCqState (rrUniform M) (rrEncoded thetaY code.encoder))
          (Real.sqrt (2 * epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
