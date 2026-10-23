-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_maximalEntropy
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.maximalEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:01:41.087772+00:00
-- url     : https://prove2.me/theorems/a91da800-9205-4ba9-b530-9f31d6abcb98
-- title:
--   Corollary A.11: Maximal observable Xobs in Xalg has H(Xobs)≥H(Xalg); maximal subalgebra Xprime in Xalg has H(Xprime)≥H(Xalg).
-- statement:
--   Fix a normalized state on the finite intrinsic algebra $\mathcal X$. An observable is maximal here when the trace of each effect is at most one, equivalently its Heisenberg map is trace nonincreasing on positive elements. An included subalgebra $\mathcal X'$ is maximal when its inclusion has that trace property. The observable may have countably many outcomes and infinite entropy.
--
--   $$
--   H(X_{\rm obs})\ge H(\mathcal X),\qquad H(\mathcal X')\ge H(\mathcal X).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 71, Corollary A.11

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary A.11, PDF p.71: both maximal-observable and maximal-subalgebra clauses.
The countable observable entropy is allowed to be infinite. -/
theorem maximalEntropy {A : IntrinsicSystem} (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    (∀ {B : Type*} [Countable B] (D : B → Matrix (Fin A.dim) (Fin A.dim) ℂ),
      IsCountablePOVM D → (∀ b, InBlocks A.block (D b)) → (∀ b, (D b).trace.re ≤ 1) →
      ENNReal.ofReal (vnEntropy rho) ≤ countableEntropy (fun b => effectProb rho (D b))) ∧
    (∀ (X : IntrinsicSystem) (E : Embedding X A), TraceNonincreasing E.toIntrinsicOperation →
      viewedEntropy X E.map rho ≥ vnEntropy rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
