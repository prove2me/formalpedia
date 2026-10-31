-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_spohn_ergodicity
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.spohn_ergodicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:23:29.724589+00:00
-- url     : https://prove2.me/theorems/83f772d1-4426-44af-a331-ed0e71d6d59a
-- title:
--   §4, (34)–(35) — finite weak-coupling ergodicity criterion
-- statement:
--   Use the finite Davies construction with all its self-adjointness, positivity and KMS assumptions. Every matrix commuting with $H$ and all the $Q_j^{(k)}$ lies in the kernel of $L=\sum_jL_j$. Consequently positivity improvement at every positive time requires
--
--   $$\{Q_j^{(k)}\}'\cap\{H\}'=\mathbb C1.$$
--
--   The bicommutant of the full family of constructed Bohr components is all of $B(\mathbb C^d)$ exactly when this scalar-commutant condition holds. If, additionally, every matrix $h_j(\omega)$ is strictly positive at every reservoir and Bohr frequency, that condition is sufficient for positivity improvement. The bicommutant equivalence is attributed by the source to Spohn. These clauses give the complete necessity and conditional sufficiency criterion.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 17, §4, (34)–(35)

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

/-- PDF p.17, (34): the complete finite Spohn criterion, including kernel inclusion,
necessity, the attributed bicommutant equivalence, and sufficiency under strict positivity. -/
theorem spohn_ergodicity {d M : ℕ} (D : DaviesData d M) :
    (∀ B ∈ commonCommutant D.H (allCouplings D), (∑ j, daviesGenerator D j) B = 0) ∧
    ((∀ t : ℝ, 0 < t → IsImproving (qdsEvolution (∑ j, daviesGenerator D j) t)) →
      commonCommutant D.H (allCouplings D) = (scalars d : Set (Mat d))) ∧
    (commutant (commutant (allBohrComponents D)) = Set.univ ↔
      commonCommutant D.H (allCouplings D) = (scalars d : Set (Mat d))) ∧
    ((∀ j w, w ∈ energyDifferenceSet D.H → (D.h j w).PosDef) →
      commonCommutant D.H (allCouplings D) = (scalars d : Set (Mat d)) →
      ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution (∑ j, daviesGenerator D j) t)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
