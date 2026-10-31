-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_perron_relaxation
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.perron_relaxation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:03:19.860527+00:00
-- url     : https://prove2.me/theorems/4b3d65d6-0309-4a67-b229-4aacf671066b
-- title:
--   Theorem 2.2 — Perron eigenvalue and exponential relaxation
-- statement:
--   Let $d>0$ and let $e^{tL}$ be a completely positive semigroup on $B(\mathbb C^d)$ which is positivity improving for every $t>0$. Set $\ell=\max\operatorname{Re}\operatorname{sp}(L)$. Then $\ell$ is an algebraically simple eigenvalue, and every other eigenvalue has real part strictly below $\ell$. For every density $\rho$ and nonzero positive matrix $X$,
--
--   $$\lim_{t\to\infty}\frac{1}{t}\log\operatorname{tr}(\rho e^{tL}(X))=\ell.$$
--
--   If the semigroup is additionally unital, $\ell=0$ and there is a faithful stationary density $\rho_+$ and $\gamma>0$ such that, for each initial density, $\|e^{tL^*}(\rho)-\rho_+\|\le C_\rho e^{-\gamma t}$ eventually. The decay exponent precedes the initial-state quantifier. This gives the spectral foundation for exponential relaxation.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 5, Theorem 2.2

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

/-- PDF pp.5,25, Theorem 2.2: algebraic simplicity and strict separation, including d=1,
where the complementary spectrum is empty. Unitality is used only in the final implication. -/
theorem perron_relaxation {d : ℕ} (hd : 0 < d) (L : GeneratorMap d)
    (hCP : IsCPSemigroup L) (hPI : ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution L t)) :
    IsPerron L (abscissa L) ∧
    (∀ rho, IsDensityMatrix rho → ∀ X : Mat d, X.PosSemidef → X ≠ 0 →
      Tendsto (fun t : ℝ => Real.log (evaluate rho (qdsEvolution L t X)) / t)
        atTop (nhds (abscissa L))) ∧
    (IsUnitalSemigroup L → abscissa L = 0 ∧
      ∃ rhoPlus : Mat d, RelaxesExponentially L rhoPlus) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
