-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_fanoBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.fanoBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:11:24.901825+00:00
-- url     : https://prove2.me/theorems/ee4e8b87-b057-4523-a9b0-192e44e32b5a
-- title:
--   Theorem A.24: For finite-alphabet Xobs, compatible Yalg and Yalg-valued guessing Yobs on SAME alphabet, Pe=1−sum_j Tr(rho XjYj) gives H(Xobs|Yal
-- statement:
--   Let $\rho$ be a normalized state, $X_{\rm obs}=(X_j)$ a POVM on a finite nonempty alphabet $X$, and $\mathcal Y$ an intrinsic subalgebra commuting with every $X_j$. Let a guessing POVM $(Y_j)$ take values in $\mathcal Y$ on the SAME alphabet. Write $h$ for binary entropy in bits; a singleton alphabet has $P_e=0$ and the continuous zero-product convention.
--
--   $$
--   P_e=1-\sum_j\operatorname{Tr}(\rho X_jY_j),\qquad H(X_{\rm obs}\mid\mathcal Y)\le h(P_e)+P_e\log_2(|X|-1).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 75, Theorem A.24

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

/-- Theorem A.24, PDF p.75: same finite nonempty alphabet for the observable and
its guess; conditioning is on the whole compatible subsystem, not just its measurement. -/
theorem fanoBound {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B] {Y A : IntrinsicSystem}
    (E : Embedding Y A) (X : B → Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hX : IsPOVM X) (hblocks : ∀ b, InBlocks A.block (X b))
    (hcompat : ∀ b T, InBlocks Y.block T → X b * E.map T = E.map T * X b)
    (guess : B → Matrix (Fin Y.dim) (Fin Y.dim) ℂ) (hguess : IsPOVM guess)
    (hguessblocks : ∀ b, InBlocks Y.block (guess b))
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    let Pe := 1 - ∑ b, effectProb rho (X b * E.map (guess b))
    vnEntropy (observableJoint E X rho) - viewedEntropy Y E.map rho ≤
      binEntropy2 Pe + Pe * Real.logb 2 (Fintype.card B - 1 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
