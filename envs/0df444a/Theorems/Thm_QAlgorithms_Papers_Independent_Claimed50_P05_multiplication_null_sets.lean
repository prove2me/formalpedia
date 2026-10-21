-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_multiplication_null_sets
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.multiplication_null_sets
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:09:34.538995+00:00
-- url     : https://prove2.me/theorems/ea358d8f-8aa1-450c-b3f1-ab35f529c77b
-- title:
--   Lemma 4.5
-- statement:
--   Let $(\Omega,\Sigma,\mu)$ be semifinite: every measurable set of infinite measure contains a measurable subset of finite positive measure. Let $\Phi(a)=M_a$ be the multiplication calculus on $L^2(\mu;k)$. For every $A\in\Sigma$,
--
--   $$\mu(A)=0\quad\Longleftrightarrow\quad\Phi(1_A)=0.$$
--
--   No sigma-finiteness is required.
--
--   This compares the multiplication calculus null ideal with the underlying measure.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 18, Lemma 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Lemma 4.5, PDF p.18: semifinite multiplication-calculus null sets are exactly measure-null sets. -/
theorem multiplication_null_sets (mu : Measure X) (hmu : Semifinite mu)
    (A : Set X) (hA : MeasurableSet A) :
    mu A = 0 ↔ Null (multiplication (k := k) mu) A := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
