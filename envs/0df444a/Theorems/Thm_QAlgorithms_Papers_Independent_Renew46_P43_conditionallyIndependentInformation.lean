-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_conditionallyIndependentInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.conditionallyIndependentInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:07:47.508494+00:00
-- url     : https://prove2.me/theorems/7d74ed06-4ce9-41be-a7fa-c2d17778360f
-- title:
--   Theorem A.17: For compatible X1,X2,Y1,Y2, I(Y1:X2Y2|X1)=I(Y2:X1Y1|X2)=0 implies I(X1X2:Y1Y2)≤I(X1:Y1)+I(X2:Y2). For n pairs, H(Yk|all X, other Y
-- statement:
--   Fix a normalized ambient state and finite families of intrinsic subalgebras $X_k,Y_k$, whose distinct members commute elementwise. Do not assume a product ambient state. The displayed conditional-entropy equations are the source conditional-independence hypotheses; their two-pair specialization is exactly the two conditional-mutual-information-zero hypotheses.
--
--   $$
--   H(Y_k\mid X_1\cdots X_nY_{\ne k})=H(Y_k\mid X_k)\ \forall k\Longrightarrow I(X_1\cdots X_n;Y_1\cdots Y_n)\le\sum_k I(X_k;Y_k).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 73, Theorem A.17

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

/-- Theorem A.17, PDF pp.73-74, including its n-fold continuation. The conditional
independence equation is exactly H(Y_k|all X,other Y)=H(Y_k|X_k); n=2 gives the
two displayed conditional-mutual-information-zero hypotheses. -/
theorem conditionallyIndependentInformation {n : ℕ} {A : Fin n × Bool → IntrinsicSystem} {C : IntrinsicSystem}
    (E : ∀ i, Embedding (A i) C) (rho : Matrix (Fin C.dim) (Fin C.dim) ℂ)
    (hrho : C.IsState rho) (hcompat : ∀ i j, i ≠ j → CommutingImages (E i).map (E j).map)
    (hindependent : ∀ k : Fin n,
      familyEntropy A (fun i => (E i).map) rho Finset.univ -
        familyEntropy A (fun i => (E i).map) rho (Finset.univ.erase (k,true)) =
      familyEntropy A (fun i => (E i).map) rho {(k,false),(k,true)} -
        familyEntropy A (fun i => (E i).map) rho {(k,false)}) :
    familyEntropy A (fun i => (E i).map) rho (xIndices n) +
      familyEntropy A (fun i => (E i).map) rho (yIndices n) -
      familyEntropy A (fun i => (E i).map) rho Finset.univ ≤
    ∑ k, (familyEntropy A (fun i => (E i).map) rho {(k,false)} +
      familyEntropy A (fun i => (E i).map) rho {(k,true)} -
      familyEntropy A (fun i => (E i).map) rho {(k,false),(k,true)}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
