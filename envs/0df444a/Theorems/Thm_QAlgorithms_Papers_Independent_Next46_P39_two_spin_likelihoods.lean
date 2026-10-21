-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_two_spin_likelihoods
-- name    : QAlgorithms.Papers.Independent.Next46.P39.two_spin_likelihoods
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:49:58.90598+00:00
-- url     : https://prove2.me/theorems/848a5a3b-6306-41da-9c98-585e5b4d7fb3
-- title:
--   Parallel, antiparallel, and optimal two-spin likelihoods
-- statement:
--   Consider the actual action $g\otimes g$ of $\mathrm{SU}(2)$ on two qubits, with normalized bi-invariant Haar measure and normalized covariant POVM densities. Write $s=(|01\rangle-|10\rangle)/\sqrt2$ and $t_0=(|01\rangle+|10\rangle)/\sqrt2$. The exact attainable maxima are
--
--   $$p_{\mathrm{opt}}(|00\rangle)=3,\qquad p_{\mathrm{opt}}(|01\rangle)=\frac{(1+\sqrt3)^2}{2},\qquad p_{\mathrm{opt}}\left(\tfrac12s+\tfrac{\sqrt3}{2}t_0\right)=4.$$
--
--   The last input is normalized, and no density matrix with a normalized covariant measurement exceeds likelihood $4$. Each stated optimum includes both its universal measurement bound and attainment. These are group-label densities, including redundant labels from stabilizers, rather than direction fidelities.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 10, §2.6 Consequence I: parallel versus antiparallel spin likelihoods

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixBorel

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

variable (R : FiniteModel G I S)

variable {R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

/-- PDF pp.10–11, Consequence I: likelihoods for the actual tensor-square
SU(2) action. All values are densities for normalized group Haar, including
when the state has a stabilizer. No direction-fidelity claim is made. -/
theorem two_spin_likelihoods (dg : Measure SpinGroup)
    (hprob : dg Set.univ = 1)
    (hleft : ∀ h, Measure.map (fun g => h * g) dg = dg)
    (hright : ∀ h, Measure.map (fun g => g * h) dg = dg) :
    SpinMaximum dg (QAlgorithms.ket (0, 0)) 3 ∧
    SpinMaximum dg (QAlgorithms.ket (0, 1)) ((1 + Real.sqrt 3) ^ 2 / 2) ∧
    QAlgorithms.IsState optimalSpin ∧ SpinMaximum dg optimalSpin 4 ∧
    (∀ rho Xi : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      QAlgorithms.IsDensityMatrix rho → SpinSeed dg Xi → likelihood Xi rho ≤ 4) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
