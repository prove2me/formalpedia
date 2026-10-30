-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma6_character
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma6_character
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:28:05.332992+00:00
-- url     : https://prove2.me/theorems/de20f694-7cc7-49f9-bc98-8f9af60cfda4
-- title:
--   Lemma 6: character of the adjoint representation
-- statement:
--   Let $G$ be a finite group and let $U:G\to U(n)$ be an ordinary irreducible unitary representation, $n>0$. For $g\in G$, put $\operatorname{Ad}_U(g)(X)=U(g)XU(g)^\dagger$ and $\chi_U(g)=\operatorname{Tr}U(g)$. In row vectorization,
--
--   $$
--   \operatorname{mat}(\operatorname{Ad}_U(g))=U(g)\otimes\overline{U(g)},\qquad \chi_{\operatorname{Ad}}(g)=\operatorname{Tr}(U(g)\otimes\overline{U(g)})=|\chi_U(g)|^2.
--   $$
--
--   This identifies the adjoint representation with the tensor-conjugate representation and determines its character.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 8, Lemma 6: character of the adjoint representation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.8, Lemma 6 Eqs.(29),(30). The second tensor factor is conjugated. -/
theorem lemma6_character (hG : Finite G) (U : UnitaryIrrep G n) (g : G) :
    rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g ∧
    Matrix.trace (rowMatrixRepresentative (conjugationMap U g)) = Matrix.trace (tensorConjugate U g) ∧
    Matrix.trace (rowMatrixRepresentative (conjugationMap U g)) = (Complex.normSq (character U g) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
