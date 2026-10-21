-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_calculus_from_pvm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.calculus_from_pvm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:15:40.039338+00:00
-- url     : https://prove2.me/theorems/e922ac87-e504-431a-b829-50acf37439b2
-- title:
--   Theorem 6.3
-- statement:
--   Let $H$ be a Hilbert space and let $E:\Sigma\to L(H)$ satisfy PVM1–PVM3: orthogonal projections, $E(X)=I$, and strong countable additivity on disjoint measurable sets. Then
--
--   $$\exists!\ \Phi:M(X)\to C(H)\text{ a measurable calculus with }\Phi(1_A)=E(A)\quad(A\in\Sigma).$$
--
--   No countability, finite dimensionality, or compactness of the base is assumed.
--
--   This constructs a unique full calculus from a projection-valued measure.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 26, Theorem 6.3

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

/-- Theorem 6.3, PDF pp.26–27: existence and uniqueness from a full arbitrary-Hilbert-space PVM. -/
theorem calculus_from_pvm (E : {A : Set X // MeasurableSet A} → Relation H)
    (hE : PVM (k := k) E) :
    ∃! F : Symbol X k → Relation H, Calculus F ∧
      ∀ A (hA : MeasurableSet A), E ⟨A, hA⟩ = F (indicator A hA) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
