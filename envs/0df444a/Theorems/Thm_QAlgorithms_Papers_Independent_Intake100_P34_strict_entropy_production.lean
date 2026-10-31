-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_strict_entropy_production
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.strict_entropy_production
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:24:16.713443+00:00
-- url     : https://prove2.me/theorems/e60a0233-e7ea-4a11-b864-6c0662148141
-- title:
--   §4 — strict entropy production criterion, with scalar-Hamiltonian exclusion
-- statement:
--   For the finite Davies construction, assume there are reservoirs $j_1,j_2$ with different positive inverse temperatures. For each of these reservoirs, assume every $h_j(\omega)$ is strictly positive and $\{Q_j^{(k)}\}_k'\cap\{H\}'=\mathbb C1$. Also assume $H\notin\mathbb C1$, so the two Gibbs densities differ. Each selected reservoir semigroup is positivity improving and has its Gibbs density as its only stationary state. For every density $\rho$, including rank-deficient densities,
--
--   $$\sigma(\rho)>0.$$
--
--   Entropy production is computed from the actual constructed dual semigroups, and the comparison permits $+\infty$. The nonscalar-Hamiltonian exclusion corrects the printed criterion's equal-Gibbs-state corner. The source credits the criterion to Lebowitz–Spohn and Aschbacher–Spohn.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 17, §4

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

/-- PDF p.17, (35), attributed to LS1/AS. SOURCE CORRECTION: exclude scalar H, since
unequal temperatures alone need not give different Gibbs states. Positivity is extended-real
at singular states; no faithfulness hypothesis is imposed on the input state. -/
theorem strict_entropy_production {d M : ℕ} (D : DaviesData d M) (j1 j2 : Fin M)
    (hBeta : D.beta j1 ≠ D.beta j2) (hNonScalar : D.H ∉ (scalars d : Set (Mat d)))
    (hPrimitive : ∀ j ∈ ({j1, j2} : Set (Fin M)),
      commonCommutant D.H (Set.range (D.Q j)) = (scalars d : Set (Mat d)))
    (hStrict : ∀ j ∈ ({j1, j2} : Set (Fin M)), ∀ w ∈ energyDifferenceSet D.H, (D.h j w).PosDef) :
    (∀ j ∈ ({j1, j2} : Set (Fin M)),
      (∀ t : ℝ, 0 < t → IsImproving (qdsEvolution (daviesGenerator D j) t)) ∧
      (∀ rho, IsDensityMatrix rho → (StationaryDensity (daviesGenerator D j) rho ↔ rho = qdsGibbsDensity D.H (D.beta j)))) ∧
    ∀ rho, IsDensityMatrix rho → 0 < daviesEntropyProduction D rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
