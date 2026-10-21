-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_canonical_transforms
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_canonical_transforms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:19:25.733367+00:00
-- url     : https://prove2.me/theorems/4bad3dbc-982b-4551-bf7b-9e07d3a27411
-- title:
--   Lemma 7.5
-- statement:
--   Let $A$ be closed and densely defined on a real or complex Hilbert space. Define $T_A=(I+A^*A)^{-1}$ and $S_A=AT_A$ as actual graph operations. Then $T_A$ is injective, bounded, positive, self-adjoint, and has norm at most one; $S_A$ is bounded; and
--
--   $$A=\overline{S_AT_A^{-1}}.$$
--
--   If $A$ is normal, then $T_{A^*}=T_A$, $S_{A^*}=S_A^*$, $A=T_A^{-1}S_A$, and $T_AS_A=S_AT_A$. Self-adjointness of $A$ implies self-adjointness of $S_A$, and normality of $A$ implies normality of $S_A$.
--
--   These canonical bounded transforms reduce the unbounded spectral theorem to bounded operators.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 34, Lemma 7.5

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

/-- Lemma 7.5, PDF p.34: canonical transforms of an arbitrary closed densely defined operator. -/
theorem spectral_canonical_transforms (A : Relation H) (hA : ClosedOperator (k := k) A)
    (hd : Dense (graphDomain A)) :
    (InjectiveOperator (transformT (k := k) A) ∧ NormBound (k := k) (transformT (k := k) A) 1 ∧
      GraphPositive (k := k) (transformT (k := k) A) ∧ SelfAdjoint (k := k) (transformT (k := k) A) ∧
      BoundedOperator (k := k) (transformS (k := k) A)) ∧
    A = closure (mul (transformS (k := k) A) (inverse (transformT (k := k) A))) ∧
    (Normal (k := k) A →
      transformT (k := k) (graphAdjoint (k := k) A) = transformT (k := k) A ∧
      transformS (k := k) (graphAdjoint (k := k) A) = graphAdjoint (k := k) (transformS (k := k) A) ∧
      A = mul (inverse (transformT (k := k) A)) (transformS (k := k) A) ∧
      mul (transformT (k := k) A) (transformS (k := k) A) = mul (transformS (k := k) A) (transformT (k := k) A)) ∧
    ((SelfAdjoint (k := k) A → SelfAdjoint (k := k) (transformS (k := k) A)) ∧
      (Normal (k := k) A → Normal (k := k) (transformS (k := k) A))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
