-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_knowledgeDecreasesUncertainty
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.knowledgeDecreasesUncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:10:41.655648+00:00
-- url     : https://prove2.me/theorems/f2841b8c-1f28-48ab-9bcd-26f34ed9e829
-- title:
--   Theorem A.23: H(psi|phi)≤H(psi|phi∘phiPrime), in particular ≤H(psi), for compatible phi,psi and arbitrary CP-unital phiPrime:Xprime→X.
-- statement:
--   Fix a normalized state and compatible CP-unital Heisenberg maps $\phi:X\to A$, $\psi:Y\to A$, together with any CP-unital map $\phi':X'\to X$. Conditional entropy is joint viewed entropy minus conditioning entropy and need not be nonnegative.
--
--   $$
--   H(\psi\mid\phi)\le H(\psi\mid\phi\circ\phi'),\qquad H(\psi\mid\phi)\le H(\psi).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 75, Theorem A.23

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

/-- Theorem A.23, PDF p.75: conditioning is weakened by Heisenberg preprocessing,
with the unconditional upper bound retained as a second conclusion. -/
theorem knowledgeDecreasesUncertainty {X Y Xnew A : IntrinsicSystem}
    (E : IntrinsicOperation X A) (F : IntrinsicOperation Y A) (hcompat : CommutingImages E.map F.map)
    (i : IntrinsicOperation Xnew X) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : A.IsState rho) :
    intrinsicConditionalEntropy Y X F.map E.map rho ≤
      intrinsicConditionalEntropy Y Xnew F.map (E.map.comp i.map) rho ∧
    intrinsicConditionalEntropy Y X F.map E.map rho ≤ viewedEntropy Y F.map rho := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
