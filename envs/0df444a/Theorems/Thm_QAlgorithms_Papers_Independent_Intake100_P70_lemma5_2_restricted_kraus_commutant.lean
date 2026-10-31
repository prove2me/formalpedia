-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P70_lemma5_2_restricted_kraus_commutant
-- name    : QAlgorithms.Papers.Independent.Intake100.P70.lemma5_2_restricted_kraus_commutant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:43:11.793604+00:00
-- url     : https://prove2.me/theorems/a33d08fd-8489-4f40-bd36-df63bf410b21
-- title:
--   Lemma 5.2: restricted adjoint fixed space is the Kraus commutant
-- statement:
--   Let $\mathcal E$ be a CPTP endomorphism on a finite-dimensional nonzero complex Hilbert space. Let $P_0$ be the computed fixed support, let $\mathcal E_0$ be its corner restriction, and choose any Kraus representation $\mathcal E(X)=\sum_iE_iXE_i^\dagger$. Put $K_i=P_0E_iP_0$. For every $X=P_0XP_0$,
--
--   $$\mathcal E_0^\dagger(X)=X\iff XK_i=K_iX\quad\text{for every }i.$$
--
--   The faithful corner operator needed in the proof is a derived fact, not another hypothesis.
-- source:
--   Information preserving structures: A general framework for quantum zero-error information, arXiv:1006.1358v1, PDF p. 22, Lemma 5.2: restricted adjoint fixed space is the Kraus commutant

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

/-- PDF pp.22–23, Lemma 5.2: for ANY Kraus representation of E, the computed
restricted adjoint fixed space is the commutant of its restricted Kraus operators. -/
theorem lemma5_2_restricted_kraus_commutant {I : Type*} [Fintype I]
    [DecidableEq I] [Nonempty I] (E : Superop I I) (hE : IsChannel E)
    (m : ℕ) (K : Fin m → Op I) (hK : ∀ X, E X = krausApply K X)
    (X : Op I) (hX : CornerSupported (fixedSupport E) X) :
    cornerAdjoint E X = X ↔ ∀ i,
      X * (fixedSupport E * K i * fixedSupport E) =
        (fixedSupport E * K i * fixedSupport E) * X := by sorry

end QAlgorithms.Papers.Independent.Intake100.P70

end
