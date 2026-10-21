-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_measurable_bounded_core
-- name    : QAlgorithms.Papers.Independent.Next46.P06.measurable_bounded_core
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:48:10.016986+00:00
-- url     : https://prove2.me/theorems/9c4750a9-cff1-4498-af17-9a8be5a1ee32
-- title:
--   §14, unnumbered: bounded symbols form a core
-- statement:
--   Let $(Z,\Sigma)$ be any measurable space and $H$ any complex Hilbert space. For a measurable calculus $\Phi:\mathcal M(Z,\Sigma)\to\mathcal C(H)$ satisfying MFC1–MFC5, let $E$ be the algebra of bounded measurable symbols. Then $E$ is an algebraic core and the full calculus coincides with the algebraic extension of its restriction to $E$:
--
--   $$ (x,y)\in\Phi(f)\iff\forall e\in E\text{ with }ef\in E,\ \Phi(ef)x=\Phi(e)y.$$
--
--   Conversely, a unital star representation on $E$ that retains weak bounded-pointwise continuity extends by this formula to a measurable calculus. The weak bp condition is part of this bounded input; no separability or sigma-finiteness assumption is imposed.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 39, §14, unnumbered: bounded symbols form a core

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

section Measurable

variable {Z H : Type*} [MeasurableSpace Z] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Section 14, PDF pp.39–40: bounded measurable symbols form an algebraic
core, the full calculus is their algebraic extension, and a bounded star
representation retaining weak bp continuity extends measurably. The last
hypothesis is not dropped. All measurable spaces and complex Hilbert spaces
are arbitrary. -/
theorem measurable_bounded_core [CompleteSpace H] (Phi : MeasurableSymbol Z → Graph H) :
    let E : Set (MeasurableSymbol Z) :=
      {e | QAlgorithms.Papers.Independent.Claimed50.P05.BoundedSymbol e}
    (QAlgorithms.Papers.Independent.Claimed50.P05.Calculus Phi →
      MeasurableAlgebraicCore Phi E ∧ (∀ f, Phi f = measurableExtension Phi E f)) ∧
    (∀ rho : MeasurableSymbol Z → Graph H, BoundedMeasurableRepresentation rho →
      QAlgorithms.Papers.Independent.Claimed50.P05.Calculus (measurableExtension rho E)) := by sorry

end Measurable

end QAlgorithms.Papers.Independent.Next46.P06

end
