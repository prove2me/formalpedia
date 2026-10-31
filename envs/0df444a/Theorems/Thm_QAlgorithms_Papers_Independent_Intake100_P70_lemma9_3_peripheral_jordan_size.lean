-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma9_3_peripheral_jordan_size
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma9_3_peripheral_jordan_size
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:48:56.531614+00:00
-- url     : https://prove2.me/theorems/caec9c4b-b1eb-4ef2-9e1b-207e41d4ecf7
-- title:
--   Lemma 9.3: peripheral Jordan blocks are one-dimensional
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $v_0,\ldots,v_{m-1}$ be an independent Jordan chain of positive length $m$ for eigenvalue $z$. If $|z|=1$, then
--
--   $$m=1.$$
--
--   Repeated unit-modulus eigenvalues in separate size-one blocks are allowed. This is peripheral semisimplicity, not an orthogonality assertion.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 27, Lemma 9.3: peripheral Jordan blocks are one-dimensional

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

/-- PDF p.27, Lemma 9.3: every peripheral Jordan block has size one, even
when several different size-one blocks have the same eigenvalue. -/
theorem lemma9_3_peripheral_jordan_size {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    {m : ℕ} (hm : 0 < m) (z : ℂ) (hz : ‖z‖ = 1)
    (v : Fin m → Op I) (hv : IsJordanChain E z v) : m = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
