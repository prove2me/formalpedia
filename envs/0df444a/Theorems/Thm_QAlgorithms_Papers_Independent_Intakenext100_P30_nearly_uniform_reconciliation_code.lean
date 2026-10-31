-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_nearly_uniform_reconciliation_code
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.nearly_uniform_reconciliation_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:52:11.273116+00:00
-- url     : https://prove2.me/theorems/67739f1b-d20e-44c6-a0db-cd62620e13e2
-- title:
--   Reconciliation under a nearly uniform input yields an affine code
-- statement:
--   Retain the channel, surjective linear compressor $f:U\to C$, and normalized decompressor family of Lemma 2. Let $P$ be an input law on $U$, and let $U_{\rm unif}$ denote the uniform law. Suppose $\varepsilon_1,\varepsilon_2\ge0$, $\tfrac12\sum_u|P(u)-|U|^{-1}|\le\varepsilon_1$, and the same reconciliation protocol has error at most $\varepsilon_2$ under $P$. There are an affine encoder $m\mapsto a+m$ from $M=\ker f$ and a normalized decoder such that
--
--   $$
--   |M|=\frac{|U|}{|C|},\qquad
--   \Pr[\widehat M\ne M]\le\varepsilon_1+\varepsilon_2
--   $$
--
--   for uniformly distributed messages. This permits the uniform-input construction to tolerate the distribution-shaping error.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 4, Remark 2: nearly uniform inputs

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

/-- Remark 2, PDF p.4, with Lemma 2's onto-range and affine-fiber corrections.
The same channel and reconciliation protocol are evaluated under the two laws. -/
theorem nearly_uniform_reconciliation_code {K : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup C] [Module K C] [Nonempty Y]
    (theta : U → Matrix Y Y ℂ) (hTheta : RRIsCq theta)
    (compress : U →ₗ[K] C) (honto : Function.Surjective compress)
    (decompress : C → U → Matrix Y Y ℂ) (hDec : ∀ c, IsPOVM (decompress c))
    (p : RRDistribution U) (epsilon1 epsilon2 : ℝ) (he1 : 0 ≤ epsilon1) (he2 : 0 ≤ epsilon2)
    (hnear : tvDist (rrUniform U) p.prob ≤ epsilon1)
    (herror : rrReconciliationError theta compress decompress p.prob ≤ epsilon2) :
    ∃ a : U, ∃ decoder : {u : U // compress u = 0} → Matrix Y Y ℂ,
      IsPOVM decoder ∧
      (Fintype.card {u : U // compress u = 0} : ℝ) =
        (Fintype.card U : ℝ) / (Fintype.card C : ℝ) ∧
      rrAffineCodeError theta compress a decoder ≤ epsilon1 + epsilon2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
