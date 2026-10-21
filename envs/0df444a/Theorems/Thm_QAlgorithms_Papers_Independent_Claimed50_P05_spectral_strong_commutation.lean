-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_strong_commutation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_strong_commutation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:20:49.883683+00:00
-- url     : https://prove2.me/theorems/3c841745-fc15-40b7-8462-7c44215c1c97
-- title:
--   Corollary 7.8
-- statement:
--   Let $A,B$ be closed densely defined normal operators, self-adjoint in the real case. Let $f(A),g(B)$ denote their canonical Borel evaluations and $Z_A,Z_B$ their bounded transforms. The following five conditions are equivalent:
--
--   $$\begin{gathered}
--   A,B\text{ strongly commute};\qquad Z_AZ_B=Z_BZ_A;\\
--   f(A)\text{ commutes with }g(B)\text{ for every measurable }f,g\text{ when at least one image is bounded};\\
--   f(A)g(B)=g(B)f(A)\text{ for every bounded measurable }f,g;\\
--   E_A(C)E_B(D)=E_B(D)E_A(C)\text{ for all Borel }C,D\subseteq k.
--   \end{gathered}$$
--
--   In the third condition, the bounded factor acts on the left in the graph-inclusion definition of commutation. If both factors are bounded this becomes equality. The fifth condition uses $E_A(C)=1_C(A)$ and $E_B(D)=1_D(B)$; strong commutation uses the four canonical transforms.
--
--   This compares transform, functional-calculus, and spectral-projection notions of strong commutation.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 36, Corollary 7.8

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

/-- Corollary 7.8, PDF p.36: five characterizations for possibly unbounded operators. -/
theorem spectral_strong_commutation (A B : Relation H)
    (hA : SpectralAdmissible (k := k) A) (hB : SpectralAdmissible (k := k) B) :
    (StronglyCommute (k := k) A B ↔
      mul (transformZ (k := k) A) (transformZ (k := k) B) = mul (transformZ (k := k) B) (transformZ (k := k) A)) ∧
    (StronglyCommute (k := k) A B ↔
      ∀ f g : Symbol k k, BoundedOperator (k := k) (spectralValue A f) ∨ BoundedOperator (k := k) (spectralValue B g) →
        (BoundedOperator (k := k) (spectralValue A f) →
          mul (spectralValue A f) (spectralValue B g) ⊆ mul (spectralValue B g) (spectralValue A f)) ∧
        (BoundedOperator (k := k) (spectralValue B g) →
          mul (spectralValue B g) (spectralValue A f) ⊆ mul (spectralValue A f) (spectralValue B g))) ∧
    (StronglyCommute (k := k) A B ↔
      ∀ f g : Symbol k k, BoundedSymbol f → BoundedSymbol g →
        mul (spectralValue A f) (spectralValue B g) = mul (spectralValue B g) (spectralValue A f)) ∧
    (StronglyCommute (k := k) A B ↔
      ∀ (C : Set k) (hC : MeasurableSet C) (D : Set k) (hD : MeasurableSet D),
        mul (spectralValue A (indicator C hC)) (spectralValue B (indicator D hD)) =
          mul (spectralValue B (indicator D hD)) (spectralValue A (indicator C hC))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
