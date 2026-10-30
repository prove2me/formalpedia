-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma54_characterMatrix
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma54_characterMatrix
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:56:20.787901+00:00
-- url     : https://prove2.me/theorems/396c32b7-cfec-4e62-a667-a942f52188b7
-- title:
--   Lemma 54: character matrix and conjugacy-class averaging projector
-- statement:
--   Let $G$ be a finite group and let $\{\varphi^\gamma\}_{\gamma\in\widehat G}$ be a complete inequivalent unitary irreducible family in fixed bases. Define the rectangular matrix $T_{g\gamma}=\chi_\gamma(g^{-1})$. Let $K(g)$ be the conjugacy class of $g$. Then
--
--   $$
--   \frac{T^\dagger T}{|G|}=I_{|\widehat G|},\qquad\left(\frac{TT^\dagger}{|G|}\right)_{gh}=\begin{cases}|K(g)|^{-1}&h\in K(g),\\0&h\notin K(g).\end{cases}
--   $$
--
--   The matrix $TT^\dagger/|G|$ is the idempotent averaging operator on conjugacy classes. Ordering elements by classes gives blocks $|K|^{-1}\mathbf 1_{|K|\times|K|}$. This statement does not require any representation $U$ to be multiplicity-free.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 23, Lemma 54: character matrix and conjugacy-class averaging projector

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

/-- PDF pp.22--23, Lemma 54 Eq.(116). The prose's T†T is corrected to TT† for the class blocks;
the essential block factor 1/|K| is retained, with no canonical irrep/class bijection. -/
theorem lemma54_characterMatrix (F : IrrepFamily G A) :
    (Fintype.card G : ℂ)⁻¹ • ((characterMatrix F)ᴴ * characterMatrix F) = 1 ∧
    (Fintype.card G : ℂ)⁻¹ • (characterMatrix F * (characterMatrix F)ᴴ) = classAverage ∧
    (classAverage (G := G)) * classAverage = classAverage := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
