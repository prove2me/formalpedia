-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_observableInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.observableInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:04:28.990907+00:00
-- url     : https://prove2.me/theorems/9345ee1a-894f-45de-9d0c-2671857c77df
-- title:
--   Theorem A.14: Compatible observables Xobs,Yobs valued in compatible Xalg,Yalg satisfy I(Xobs:Yobs)≤I(Xalg:Yobs)≤I(Xalg:Yalg).
-- statement:
--   Fix one normalized ambient state. Let countable observables $X_{\rm obs},Y_{\rm obs}$ take values in the compatible finite intrinsic subalgebras $\mathcal X,\mathcal Y$. Classical information is defined by relative entropy of the actual joint outcome law, and hybrid information by mean posterior-state divergence; thus no difference of two infinite entropies is used.
--
--   $$
--   I(X_{\rm obs};Y_{\rm obs})\le I(\mathcal X;Y_{\rm obs})\le I(\mathcal X;\mathcal Y).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 72, Theorem A.14

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

/-- Theorem A.14, PDF p.72: both inequalities, using countable outcome laws and
divergence-defined hybrid information rather than infinity-minus-infinity. -/
theorem observableInformation {X Y A : IntrinsicSystem} {B D : Type*} [Countable B] [Countable D]
    (E : Embedding X A) (F : Embedding Y A) (hcompat : CommutingImages E.map F.map)
    (U : B → Matrix (Fin X.dim) (Fin X.dim) ℂ) (V : D → Matrix (Fin Y.dim) (Fin Y.dim) ℂ)
    (hU : IsCountablePOVM U) (hV : IsCountablePOVM V)
    (hUX : ∀ b, InBlocks X.block (U b)) (hVY : ∀ b, InBlocks Y.block (V b))
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    measuredInformation (fun b => E.map (U b)) (fun b => F.map (V b)) rho ≤
      hybridInformation X E (fun b => F.map (V b)) rho ∧
    hybridInformation X E (fun b => F.map (V b)) rho ≤
      ENNReal.ofReal (intrinsicMutualInformation X Y E.map F.map rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
