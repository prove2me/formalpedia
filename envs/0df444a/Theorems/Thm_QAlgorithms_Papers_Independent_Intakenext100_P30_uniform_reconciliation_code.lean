-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P30_uniform_reconciliation_code
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P30.uniform_reconciliation_code
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:51:37.046306+00:00
-- url     : https://prove2.me/theorems/2afa16c1-1663-4ce1-aa47-902d3945617d
-- title:
--   An affine channel code from linear reconciliation of uniform inputs
-- statement:
--   Let $U$ and $C$ be finite vector spaces over the same field, let $f:U\to C$ be a surjective linear compressor, and let $D_c$ be a normalized POVM on the receiver output with outcomes in $U$ for each $c\in C$. For a cq channel $u\mapsto\rho_Y^u$, suppose the reconciliation error under the uniform input law is at most $\varepsilon$, where $\varepsilon\ge0$. There exist $a\in U$ and a normalized decoder with message alphabet $M=\ker f$ and encoder $m\mapsto a+m$ such that
--
--   $$
--   |M|=\frac{|U|}{|C|},\qquad
--   \frac1{|M|}\sum_{m\in M}\Pr[\widehat m\ne m\mid\rho_Y^{a+m}]\le\varepsilon.
--   $$
--
--   Thus a single affine fiber of the compressor supports a channel code of the indicated size. The source's construction, rather than an assumed good fiber, supplies this code.
--
--   All alphabets are finite and nonempty, and output Hilbert spaces are finite dimensional and nonzero. A classical–quantum channel assigns a positive semidefinite, trace-one matrix to each input. Encoders may use private randomness; decoders are normalized POVMs. Codes are fixed independently of the message, with no supplied shared key or entanglement. Logarithms and entropies are in bits.
-- source:
--   Noisy channel coding via privacy amplification and information reconciliation, arXiv:1012.4814v2, PDF p. 3, Lemma 2: Channel Coding from Information Reconciliation of Uniform Inputs

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

/-- Lemma 2, PDF pp.3–4, with three source corrections: the compression map is
onto its actual range; the encoder is the affine inclusion m ↦ a+m into a fiber;
the error conclusion is <= epsilon, matching the definition of epsilon-good.
No good fiber or resulting error bound is a hypothesis. -/
theorem uniform_reconciliation_code {K : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup C] [Module K C] [Nonempty Y]
    (theta : U → Matrix Y Y ℂ) (hTheta : RRIsCq theta)
    (compress : U →ₗ[K] C) (honto : Function.Surjective compress)
    (decompress : C → U → Matrix Y Y ℂ) (hDec : ∀ c, IsPOVM (decompress c))
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (herror : rrReconciliationError theta compress decompress (rrUniform U) ≤ epsilon) :
    ∃ a : U, ∃ decoder : {u : U // compress u = 0} → Matrix Y Y ℂ,
      IsPOVM decoder ∧
      (Fintype.card {u : U // compress u = 0} : ℝ) =
        (Fintype.card U : ℝ) / (Fintype.card C : ℝ) ∧
      rrAffineCodeError theta compress a decoder ≤ epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P30

end
