-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_commutant
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_commutant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:20:21.950222+00:00
-- url     : https://prove2.me/theorems/6a58dd7c-18a8-4d32-b1b9-722584feb423
-- title:
--   Proposition 7.7
-- statement:
--   Let $A$ be closed densely defined normal on a $k$-Hilbert space, self-adjoint if $k=\mathbb R$, and let $B\in L(H)$. Write $f(A)$ for its canonical Borel evaluation, $T_A=(I+A^*A)^{-1}$, $S_A=AT_A$, and $Z_A=(z/\sqrt{1+|z|^2})(A)$. Then
--
--   $$BA\subseteq AB\ \Longleftrightarrow\ (\forall f\in M(k))\ Bf(A)\subseteq f(A)B\ \Longleftrightarrow\ BZ_A=Z_AB\ \Longleftrightarrow\ BT_A=T_AB\text{ and }BS_A=S_AB.$$
--
--   If the same bounded $B$ is also normal, and self-adjoint in the real case, these conditions are equivalent to strong commutation of $A,B$ and to $Z_AZ_B=Z_BZ_A$. Strong commutation means pairwise commutation of their four canonical transforms.
--
--   This characterizes bounded commutants of an unbounded spectral calculus.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 36, Proposition 7.7

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

/-- Proposition 7.7, PDF p.36: both equivalence blocks for a bounded commutant B. -/
theorem spectral_commutant (A : Relation H) (hA : SpectralAdmissible (k := k) A) (B : H →L[k] H) :
    ((mul (boundedGraph B) A ⊆ mul A (boundedGraph B)) ↔
      ∀ f, mul (boundedGraph B) (spectralValue (k := k) A f) ⊆ mul (spectralValue (k := k) A f) (boundedGraph B)) ∧
    ((mul (boundedGraph B) A ⊆ mul A (boundedGraph B)) ↔
      mul (boundedGraph B) (transformZ (k := k) A) = mul (transformZ (k := k) A) (boundedGraph B)) ∧
    ((mul (boundedGraph B) A ⊆ mul A (boundedGraph B)) ↔
      mul (boundedGraph B) (transformT (k := k) A) = mul (transformT (k := k) A) (boundedGraph B) ∧
      mul (boundedGraph B) (transformS (k := k) A) = mul (transformS (k := k) A) (boundedGraph B)) ∧
    (SpectralAdmissible (k := k) (boundedGraph B) →
      ((mul (boundedGraph B) A ⊆ mul A (boundedGraph B)) ↔ StronglyCommute (k := k) A (boundedGraph B)) ∧
      ((mul (boundedGraph B) A ⊆ mul A (boundedGraph B)) ↔
        mul (transformZ (k := k) A) (transformZ (k := k) (boundedGraph B)) =
          mul (transformZ (k := k) (boundedGraph B)) (transformZ (k := k) A))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
