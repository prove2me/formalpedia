-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P89_rkhs_orthonormal_expansion
-- name    : QAlgorithms.Papers.Independent.Intake100.P89.rkhs_orthonormal_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:43:16.763335+00:00
-- url     : https://prove2.me/theorems/38afb0ce-36f8-40eb-ad7e-834412308aa6
-- title:
--   Theorem 4.3: almost sure expansion in any RKHS orthonormal basis
-- statement:
--   Let $W$ be a Borel centered Gaussian element of a real separable Banach space. For every complete orthonormal system $(h_i)$ in its RKHS, the canonical coordinates $(Uh_i)$ are independent standard normals and
--   $$W=\sum_i(Uh_i)h_i\quad\text{in }B,\quad P\text{-almost surely}.$$
--   The statement includes finite and empty complete systems, with finite or zero sums, as well as the countably infinite case with convergence of ordered partial sums.
-- source:
--   Reproducing kernel Hilbert spaces of Gaussian priors, arXiv:0805.3252v1, PDF p. 13, Theorem 4.3: almost sure expansion in any RKHS orthonormal basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P89

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P89

universe u v w

variable {Omega : Type u} [MeasurableSpace Omega]

section MoreResults

variable (P : Measure Omega) [hP : IsProbabilityMeasure P]

include hP

/-- Theorem 4.3: almost sure expansion in any RKHS orthonormal basis, arXiv:0805.3252v1, PDF p.13.
Finite/empty and infinite systems are separate clauses of one headline. L² coordinate representatives are only relevant a.s.; ordered convergence avoids an unintended unconditional sample-series claim. -/
theorem rkhs_orthonormal_expansion
{B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [TopologicalSpace.SeparableSpace B]
    (W : Omega → B) (hW : BorelCenteredGaussianElement P W) :
    (∀ (n : ℕ) (e : Fin n → banachChaos P W), Orthonormal ℝ e →
      (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ →
      StandardNormals P (fun i o => (e i : L2 P) o) ∧
      ∀ᵐ o ∂P, W o = ∑ i, (e i : L2 P) o • synthesis P W (e i : L2 P)) ∧
    (∀ e : ℕ → banachChaos P W, Orthonormal ℝ e →
      (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ →
      StandardNormals P (fun i o => (e i : L2 P) o) ∧
      ∀ᵐ o ∂P, Tendsto
        (fun n => ∑ i ∈ Finset.range n, (e i : L2 P) o • synthesis P W (e i : L2 P))
        atTop (𝓝 (W o))) := by sorry

end MoreResults

end QAlgorithms.Papers.Independent.Intake100.P89

end
