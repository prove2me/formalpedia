-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma9_maximum_unitarily_noiseless_shape
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma9_maximum_unitarily_noiseless_shape
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:38:35.5782+00:00
-- url     : https://prove2.me/theorems/33e3195a-b9d5-4b12-996e-5988cee17074
-- title:
--   Lemma 9: maximum unitarily noiseless codes have the rotating-state shape
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Maximum means that no code satisfying the same criterion has a proper subset 1-isometric to $C$. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. Let $\operatorname{Rot}(\mathcal E)$ be the complex span of eigenoperators with eigenvalues of modulus one. If $C$ is maximum among convex codes preserved by every power of $\mathcal E$, there exists a CPTP spectral projection $F$, obtained along an unbounded sequence of positive powers, such that
--
--   $$F^2=F,\quad\operatorname{ran}F=\operatorname{Fix}(F)=\operatorname{Rot}(\mathcal E),\qquad F:C\simeq_1\operatorname{Rot}(\mathcal E)_+.$$
--
--   Thus the isometric image is the entire peripheral state set. No limit of the complete power sequence is asserted.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 16, Lemma 9: maximum unitarily noiseless codes have the rotating-state shape

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

/-- PDF pp.16,26–28, Lemma 9. Rotating points are a complex span.
A subsequential CPTP spectral projection gives the isometry ONTO all its states;
the complete power sequence is not asserted to converge. -/
theorem lemma9_maximum_unitarily_noiseless_shape {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (C : Set (Op I)) (hC : MaximumCode (UnitarilyNoiseless E) C) :
    ∃ F : Superop I I, IsPeripheralProjection E F ∧
      IsCodeIsometry F C (statePart (rotatingSpace E : Set (Op I))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
