-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_unitarily_noiseless_spectral_procedure
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.unitarily_noiseless_spectral_procedure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:53:57.485014+00:00
-- url     : https://prove2.me/theorems/b21447b5-a09c-4620-a1fd-1547d16de101
-- title:
--   Unnumbered: correctness of the peripheral-IPS spectral procedure
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Extract instead the complex spans of all right and left unit-modulus eigenoperators. Their right support equals the fixed support $P_0$. There are canonical coordinates $B$ with
--
--   $$\operatorname{supp}\operatorname{Rot}(\mathcal E)=P_0,\qquad A_B=P_0\operatorname{Rot}(\mathcal E^\dagger)P_0.$$
--
--   Every maximum convex density code preserved by every power of $\mathcal E$ is 1-isometric onto $(A_B)_+$. The procedure uses peripheral spans, not just eigenvalue one; no normality or runtime assumption is added.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 16, Unnumbered: correctness of the peripheral-IPS spectral procedure

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

/-- PDF p.16, step 2': peripheral spectral procedure. Rot denotes complex
spans, not eigenvalue-1 fixed spaces. The rotating and fixed supports agree. -/
theorem unitarily_noiseless_spectral_procedure {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E) :
    jointSupport (rotatingSpace E : Set (Op I)) = fixedSupport E ∧
    ∃ B : BlockModel I, B.support = fixedSupport E ∧
      B.algebra = (fun X => fixedSupport E * X * fixedSupport E) ''
        (rotatingSpace (channelAdjoint E) : Set (Op I)) ∧
      ∀ C, MaximumCode (UnitarilyNoiseless E) C →
        OneIsometric C (statePart B.algebra) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
