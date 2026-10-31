-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_detailed_balance_structure
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.detailed_balance_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:09:41.049841+00:00
-- url     : https://prove2.me/theorems/55dfacc9-d96f-4916-87bb-19b812b5f171
-- title:
--   Theorem 7.1 — full detailed-balance structure and deformations
-- statement:
--   Let $d>0$, let $\rho$ be faithful, and fix $L=i[T,\cdot]-\{\Phi(1),\cdot\}/2+\Phi$ generating a unital CP semigroup, with $T=T^*$, $\Phi$ CP, $L^*(\rho)=0$, and $\Phi^\rho=\Phi$. Adjoints use $\operatorname{tr}(X^*Y)$ or $\operatorname{tr}(\rho X^*Y)$ as indicated. Then $(L+L^\rho)/2=-\{\Phi(1),\cdot\}/2+\Phi$ and $(L-L^\rho)/2=i[T,\cdot]$. Both parts, $L$ and $\Phi$ commute with $\Delta_\rho(X)=\rho X\rho^{-1}$; $T$ and $\Phi(1)$ commute with $\rho$, and both parts leave $\rho$ stationary.
--
--   With $P_a$ the spectral projections of $\log\rho$, define $\Phi_\omega(X)=\sum_{a-b=c-e=\omega}P_b\Phi(P_aXP_c)P_e$. These constructed components are CP, sum to $\Phi$, and satisfy
--
--   $$\Phi_\omega(X\rho^{-z})\rho^z=e^{-z\omega}\Phi_\omega(X),\quad\Phi_\omega^\rho=\Phi_{-\omega},\quad\Phi_\omega^*=e^\omega\Phi_{-\omega}.$$
--
--   For $R_\rho^z(X)=\rho^zX\rho^z$ and $L_z=R_\rho^{z/2}LR_\rho^{-z/2}$,
--
--   $$L_z(X)=L(X\rho^{-z})\rho^z=i[T,X]-\tfrac12\{\Phi(1),X\}+\sum_\omega e^{-z\omega}\Phi_\omega(X).$$
--
--   Real deformations generate CP semigroups. If the pair is time reversible under $\Theta$, then $\Theta L_a^*=L_{1-a}\Theta$ for every real $a$. These five clauses supply the structural decomposition behind the fluctuation theorem.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 21, Theorem 7.1

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

/-- PDF pp.21–23, Theorem 7.1, all five parts. The frequency components are computed by
p.22's spectral-projection formula. Both R factors have the same exponent. -/
theorem detailed_balance_structure {d : ℕ} (hd : 0 < d) (rho T : Mat d) (L Phi : GeneratorMap d)
    (hrho : Faithful rho) (hT : T.IsHermitian)
    (hPhi : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (hL : L = lindblad T Phi) (hQDS : IsQDS L)
    (hStationary : StationaryDensity L rho) (hSymmetric : weightedAdjoint rho Phi = Phi) :
    (∀ X, ((1 / 2 : ℂ) • (L + weightedAdjoint rho L)) X =
      -(1 / 2 : ℂ) • (Phi 1 * X + X * Phi 1) + Phi X) ∧
    (1 / 2 : ℂ) • (L - weightedAdjoint rho L) = hamiltonianPart T ∧
    (∀ F ∈ ({L, hamiltonianPart T, L - hamiltonianPart T, Phi} : Set (GeneratorMap d)),
      F.comp (densityModularAction rho 1) = (densityModularAction rho 1).comp F) ∧
    T * rho = rho * T ∧ Phi 1 * rho = rho * Phi 1 ∧
    StationaryDensity (L - hamiltonianPart T) rho ∧ StationaryDensity (hamiltonianPart T) rho ∧
    Phi = ∑ w ∈ frequencies rho, frequencyComponent rho Phi w ∧
    (∀ w ∈ frequencies rho,
      QAlgorithms.Entanglement.IsCompletelyPositive (frequencyComponent rho Phi w) ∧
      (∀ z : ℂ, ∀ X : Mat d,
        frequencyComponent rho Phi w (X * densityComplexPower rho (-z)) * densityComplexPower rho z =
          Complex.exp (-z * (w : ℂ)) • frequencyComponent rho Phi w X) ∧
      weightedAdjoint rho (frequencyComponent rho Phi w) = frequencyComponent rho Phi (-w) ∧
      hsAdjoint (frequencyComponent rho Phi w) =
        (Real.exp w : ℂ) • frequencyComponent rho Phi (-w)) ∧
    (∀ z : ℂ, ∀ X : Mat d,
      deformation rho L z X = L (X * densityComplexPower rho (-z)) * densityComplexPower rho z ∧
      deformation rho L z X = hamiltonianPart T X -
        (1 / 2 : ℂ) • (Phi 1 * X + X * Phi 1) +
        ∑ w ∈ frequencies rho, Complex.exp (-z * (w : ℂ)) • frequencyComponent rho Phi w X) ∧
    (∀ a : ℝ, IsCPSemigroup (deformation rho L (a : ℂ))) ∧
    (∀ Theta : Mat d → Mat d, TimeReversible rho L Theta → ∀ a : ℝ, ∀ X : Mat d,
      Theta (hsAdjoint (deformation rho L (a : ℂ)) X) =
        deformation rho L ((1 - a : ℝ) : ℂ) (Theta X)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
