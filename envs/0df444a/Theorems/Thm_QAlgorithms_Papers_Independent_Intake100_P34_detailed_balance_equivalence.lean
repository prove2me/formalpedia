-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_detailed_balance_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.detailed_balance_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:11:33.394073+00:00
-- url     : https://prove2.me/theorems/29eae0b5-9391-4875-9492-38003372e38d
-- title:
--   Theorem 7.2 — equivalent detailed-balance definitions
-- statement:
--   Let $\rho$ be a faithful density on $B(\mathbb C^d)$, $d>0$, and let $L$ generate a unital completely positive semigroup with $L^*(\rho)=0$. Then
--
--   $$\exists T=T^*:\ \frac{L-L^\rho}{2}=i[T,\cdot]\quad\Longleftrightarrow\quad\exists T=T^*,\Phi\in\mathrm{CP}:\ L=i[T,\cdot]-\tfrac12\{\Phi(1),\cdot\}+\Phi,\ \Phi^\rho=\Phi.$$
--
--   The two existential statements have independent witnesses. The displayed difference is the anti-Hermitian part, correcting the page's verbal label while preserving its formula. This establishes equivalence of the two detailed-balance formulations.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 24, Theorem 7.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.24, Theorem 7.2. The displayed (L-L^rho)/2 is anti-Hermitian; the page calls it
Hermitian. The formula is preserved and the two existential witnesses are separately scoped. -/
theorem detailed_balance_equivalence {d : ℕ} (hd : 0 < d) (rho : Mat d) (L : GeneratorMap d)
    (hrho : Faithful rho) (hQDS : IsQDS L) (hStationary : StationaryDensity L rho) :
    (∃ T : Mat d, T.IsHermitian ∧
      (1 / 2 : ℂ) • (L - weightedAdjoint rho L) = hamiltonianPart T) ↔
    (∃ T : Mat d, T.IsHermitian ∧ ∃ Phi : GeneratorMap d,
      QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧
      L = lindblad T Phi ∧ weightedAdjoint rho Phi = Phi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
