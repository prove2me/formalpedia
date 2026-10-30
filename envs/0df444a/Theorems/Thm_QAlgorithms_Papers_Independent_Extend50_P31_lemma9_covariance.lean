-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma9_covariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P31.lemma9_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:29:10.508553+00:00
-- url     : https://prove2.me/theorems/073344d3-6bb2-4285-baea-09426952d3f3
-- title:
--   Lemma 9: covariance is a matrix commutant condition
-- statement:
--   Let $G$ be finite, let $U:G\to U(n)$ be unitary irreducible with $n>0$, and let $\Phi:M_n(\mathbb C)\to M_n(\mathbb C)$ be complex-linear. Covariance is equivalent to the matrix commutant condition:
--
--   $$
--   \bigl[\forall g,X,\ \Phi(U(g)XU(g)^\dagger)=U(g)\Phi(X)U(g)^\dagger\bigr]\ \Longleftrightarrow\ \operatorname{mat}(\Phi)\in\operatorname{Int}_G(U\otimes\overline U).
--   $$
--
--   This transfers covariance to a matrix commutant without complete positivity or multiplicity-freeness assumptions.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, PDF p. 8, Lemma 9: covariance is a matrix commutant condition

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

/-- PDF pp.8--9, Lemma 9 Eq.(32), Appendix A p.34. No CP or MF premise. -/
theorem lemma9_covariance (hG : Finite G) (U : UnitaryIrrep G n) (Phi : EndMat n) :
    IsIrrepCovariant U Phi ↔ rowMatrixRepresentative Phi ∈ representationCommutant (tensorConjugate U) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P31

end
