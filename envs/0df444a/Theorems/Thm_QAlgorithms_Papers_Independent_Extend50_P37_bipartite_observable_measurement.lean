-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_bipartite_observable_measurement
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.bipartite_observable_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:44:40.981059+00:00
-- url     : https://prove2.me/theorems/1dc51278-5f8a-415d-86d3-63cb9681f7b9
-- title:
--   VI B: a fixed sequential quantum measurement suffices for the product prior
-- statement:
--   Let $H$ be Hermitian, $\mathcal A=\operatorname{Alg}(H,I)$, and draw $\rho_1,\rho_2$ independently from the same unitarily invariant density-matrix probability law. Let the finite real measurable parameter vector on their product be invariant under exchange and collective $G_{\mathcal A}$. A joint spectral PVM of $H$ can be fixed so that every POVM is simulated, for parameter-conditioned statistics, by measuring the coherent symmetric/antisymmetric sector, then that PVM individually on both systems, then stochastic processing:
--   $$q_M(B\mid s\in\Delta)=q_{M'}(B\mid s\in\Delta).$$
--   Only the classical rule depends on $M$. This includes the absolute difference and sum of expectations and all real-valued invariant examples stated on p.32.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 32, VI B: a fixed sequential quantum measurement suffices for the product prior

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.32, VI B: one fixed sector measurement and one fixed individual
spectral measurement suffice. Only the stochastic postprocessing varies.
The conditions on f include all real-valued swap-invariant examples on p.32. -/
theorem bipartite_observable_measurement [Nonempty I] {O : Type*} [MeasurableSpace O]
    {l : ℕ} (H : Mat I) (hH : H.IsHermitian)
    (p0 : EstimationPrior I 0) (hp0 : Symmetry p0 (unitaryCentralizer ({1} : Set (Mat I))))
    (f : Mat I × Mat I → Fin l → ℝ) (hf : Measurable f)
    (hswap : ∀ rho ∈ p0.support, ∀ sigma ∈ p0.support, f (rho,sigma) = f (sigma,rho))
    (hinv : ∀ rho ∈ p0.support, ∀ sigma ∈ p0.support, ∀ U ∈ unitaryCentralizer (observableAlgebra H : Set (Mat I)),
      f (U * rho * Uᴴ, U * sigma * Uᴴ) = f (rho,sigma)) :
    ∃ S : GeneratorSpectralPVM (observableAlgebra H),
      ∀ M : Measurements.OperatorPOVM (Fin 2 → I) O,
        ∃ N : Measurements.OperatorPOVM (Fin 2 → I) O,
          (∃ K : Bool → (Fin 2 → Fin S.count) → Measure O,
            (∀ s z, IsProbabilityMeasure (K s z)) ∧
            ∀ B, MeasurableSet B → N.operator B =
              (∑ z : Fin 2 → Fin S.count, ((K false z B).toReal : ℂ) •
                (permutationSector I 2 false * orderedTensorProduct (fun i => S.projector (z i)) * permutationSector I 2 false)) +
              (∑ z : Fin 2 → Fin S.count, ((K true z B).toReal : ℂ) •
                (permutationSector I 2 true * orderedTensorProduct (fun i => S.projector (z i)) * permutationSector I 2 true))) ∧
          SampleConditionals (p0.law.prod p0.law) f (fun x => pairDensity x.1 x.2)
            M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
