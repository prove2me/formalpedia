-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_cartesianFrameOptimum
-- name    : QAlgorithms.Papers.Independent.Next46.P36.cartesianFrameOptimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:43:19.481668+00:00
-- url     : https://prove2.me/theorems/d8a97f74-5174-4fcd-be05-60a7296e72d4
-- title:
--   Optimal Cartesian-frame alignment without an external reference
-- statement:
--   Alice transmits $N$ spin-one-half systems, with no external reference and a Haar-uniform unknown rotation. The physical action is $U^{\otimes N}$ of $SU(2)$, and the Cartesian error is $e(\hat g,g)=6-2\chi_1(\hat gg^{-1})=8-2|\operatorname{Tr}(U_g^\dagger U_{\hat g})|^2$.
--
--   For every $N\ge2$, there is an actual exhaustive spin decomposition, with $d_j=2j+1$ and $m_j\ge d_j$ for $j<N/2$. The fixed basis embeds $\bigoplus_{j<N/2}H_j\otimes\mathbb C^{d_j}$ into the physical space by taking the first $d_j$ multiplicity coordinates. Suitable nonnegative unit coefficients give the input $A=\bigoplus_{j<N/2}v_j\operatorname{vec}(I_j)/\sqrt{d_j}$ and seed vector $\eta=\bigoplus_{j<N/2}\sqrt{d_j}\operatorname{vec}(I_j)$. Completing the covariant density by the identity on the orthogonal complement gives a legal physical POVM. It is optimal among all inputs in the entire truncated physical sector and all joint measurements.
--
--   If $E_N$ denotes these protocols' attained errors and $e_{\rm opt}(N)$ is the infimum over all physical $N$-spin density matrices and all joint POVMs, then, across both parities,
--
--   $$\lim_{N\to\infty}N^2E_N=\lim_{N\to\infty}N^2e_{\rm opt}(N)=8\pi^2.$$
--
--   The finite truncated protocol and its asymptotic global optimality are both asserted. No reference-extension lemma is used on the physical task.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 8, §IV A, Eqs. (49)-(51)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF p.8 Eqs.(49)-(51): optimal truncated input and explicit covariant seed,
followed by the leading asymptotic GLOBAL optimum for both parities. The seed
is completed by the orthogonal complement to normalize a POVM on all N spins.
No external-reference register occurs in the comparison domain. -/
theorem cartesianFrameOptimum
    [IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)] [BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (dg : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ)) [IsProbabilityMeasure dg]
    [Measure.IsMulLeftInvariant dg] [Measure.IsMulRightInvariant dg] :
    (∃ e : ℕ → ℝ,
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * e N) atTop (nhds (8 * Real.pi ^ 2)) ∧
      ∀ N : ℕ, 2 ≤ N →
      ∃ D : Fin (N / 2 + 1) → BasedIrrep (Matrix.specialUnitaryGroup (Fin 2) ℂ),
        OccurringIrrepsInequivalent D ∧ (∀ k, (D k).dim = twiceSpin N k + 1) ∧
      ∃ B : BasedDecomposition (actualTensorRepresentation 2 N) D,
        (∀ k : Fin (N / 2), (D k.castSucc).dim ≤ B.multiplicity k.castSucc) ∧
        (frameEmbedding D B)ᴴ * frameEmbedding D B = 1 ∧
      ∃ v : Fin (N / 2) → ℝ,
        (∀ k, 0 ≤ v k) ∧ (∑ k, (v k) ^ 2) = 1 ∧
      ∃ psi eta : EuclideanSpace ℂ (TensorRegister 2 N),
        psi = WithLp.toLp 2 ((frameEmbedding D B).mulVec (WithLp.ofLp
          (canonicalInput (fun k : Fin (N / 2) => D k.castSucc) (fun k => (v k : ℂ)) (fun _ => 1)))) ∧
        eta = WithLp.toLp 2 ((frameEmbedding D B).mulVec (WithLp.ofLp
          (componentVector (fun k : Fin (N / 2) => D k.castSucc) (fun _ => 1)))) ∧
        QAlgorithms.IsState psi ∧
      ∃ M : QAlgorithms.Measurements.DensityPOVM (TensorRegister 2 N) (Matrix.specialUnitaryGroup (Fin 2) ℂ),
        M.reference = dg ∧
        (∀ g, M.density g = QAlgorithms.conjSuperop (actualTensorRepresentation 2 N g) (QAlgorithms.pureDensity eta) +
          (1 - frameEmbedding D B * (frameEmbedding D B)ᴴ)) ∧
        RepresentationAdmissible (actualTensorRepresentation 2 N) dg frameCost (QAlgorithms.pureDensity psi) M ∧
        representationRisk (actualTensorRepresentation 2 N) dg frameCost (QAlgorithms.pureDensity psi) M = e N ∧
        (∀ rho L, RepresentationAdmissible (actualTensorRepresentation 2 N) dg frameCost rho L →
          rho = truncatedFrameProjector D B * rho * truncatedFrameProjector D B →
          representationRisk (actualTensorRepresentation 2 N) dg frameCost (QAlgorithms.pureDensity psi) M ≤
            representationRisk (actualTensorRepresentation 2 N) dg frameCost rho L)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * optimalFrameRisk dg N) atTop
      (nhds (8 * Real.pi ^ 2)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
