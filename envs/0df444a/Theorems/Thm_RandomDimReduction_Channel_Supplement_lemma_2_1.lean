-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_Supplement_lemma_2_1
-- name    : RandomDimReduction.Channel.Supplement.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T21:41:47.539445+00:00
-- url     : https://prove2.me/theorems/c80834db-28ea-4701-9608-cc6faad5a005
-- title:
--   Lemma 2.1 — maximally entangled identities
-- statement:
--   Let $A,B$ be arbitrary finite-dimensional complex Hilbert spaces with fixed orthonormal bases, and let $|\Gamma_A\rangle=\sum_i|i,i\rangle$ be unnormalized. For every rectangular operator $X:A\to B$,
--   $$(I_A\otimes X)|\Gamma_A\rangle=(X^T\otimes I_B)|\Gamma_B\rangle.$$
--   For every independent pair $X,Y:A\to B$,
--   $$\operatorname{tr}_{A}\big((X\otimes I_A)|\Gamma_A\rangle\langle\Gamma_A|(Y^\dagger\otimes I_A)\big)=XY^\dagger.$$
--   The partial trace retains the first, $B$, output. These two identities support the Choi construction in Theorem 3.1.
--
--   Differences from the source:
--   - encoding: arbitrary finite-dimensional Hilbert spaces with fixed orthonormal bases → complex matrices on arbitrary finite basis types, with a product index for tensor registers; reason: every such Hilbert space admits these coordinates; empty basis types satisfy the same identities
--   - encoding: trace over the A register in the B tensor A output → partialTraceRight; reason: the second tensor factor is the discarded A register, so the retained output is XY†
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf, Lemma 2.1, p. 5

import Definitions.Def_RandomDimReduction_Channel_Supplement_Purification

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Kronecker Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel.Supplement

/-- Lemma 2.1, p.5: both identities, with arbitrary rectangular X and independent X,Y.
The trace in clause two discards the second A register, retaining the B output. -/
theorem lemma_2_1 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    (∀ X : Matrix b a ℂ,
      ((1 : Op a) ⊗ₖ X).mulVec (gamma a) =
        (Xᵀ ⊗ₖ (1 : Op b)).mulVec (gamma b)) ∧
    (∀ X Y : Matrix b a ℂ,
      WildeQIT.partialTraceRight
        ((X ⊗ₖ (1 : Op a)) * MixedCloning.Optimal.pure (gamma a) *
          (Yᴴ ⊗ₖ (1 : Op a))) = X * Yᴴ) := by sorry

end RandomDimReduction.Channel.Supplement
