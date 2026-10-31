-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma2_noiseless_embeds_in_fixed
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma2_noiseless_embeds_in_fixed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:33:45.750793+00:00
-- url     : https://prove2.me/theorems/4a44b9f3-c644-4670-aca5-bddd091a0269
-- title:
--   Lemma 2: noiseless codes embed isometrically in fixed states
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. A 1-isometry is a complex-linear identification of the code spans that maps the normalized state sets bijectively and preserves every weighted trace-norm distance. Let $C$ be a convex noiseless density code. There exists a CPTP map $F$ given by the Cesaro limit
--
--   $$F(X)=\lim_{N\to\infty}\frac1{N+1}\sum_{n=0}^{N}\mathcal E^n(X),\qquad \operatorname{ran}F=\operatorname{Fix}(\mathcal E),\quad C\simeq_1F(C)\subseteq\operatorname{Fix}(\mathcal E)_+.$$
--
--   The existence of the limit and the channel property are conclusions. Maximum is not required.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 8, Lemma 2: noiseless codes embed isometrically in fixed states

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

/-- PDF pp.8,22, Lemma 2. The Cesaro limit exists and is CPTP; its isometric
image of C is a subset of fixed states, without a maximum assumption. -/
theorem lemma2_noiseless_embeds_in_fixed {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (C : Set (Op I)) (hC : IsCode C) (hN : Noiseless E C) :
    ∃ F : Superop I I, IsChannel F ∧
      (∀ X, Tendsto (fun N => cesaroAverage E N X) atTop (nhds (F X))) ∧
      Set.range F = fixedOperators E ∧
      IsCodeIsometry F C (F '' C) ∧ F '' C ⊆ fixedStates E := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
