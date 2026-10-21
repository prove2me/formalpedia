-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_compact_formal_dimension
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.compact_formal_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:05:27.506456+00:00
-- url     : https://prove2.me/theorems/42bd7dbe-9d55-49a3-8947-55db9a1c78c8
-- title:
--   §III: formal dimension for compact G
-- statement:
--   Let $G$ be compact, with probability Haar measure, and let $\mathcal H_\mu$ be a nonzero irreducible component of its strongly continuous projective unitary action on a complete complex Hilbert space. Then $\mathcal H_\mu$ is finite dimensional and, writing $d_\mu=\dim\mathcal H_\mu>0$, every unit vector $v\in\mathcal H_\mu$ satisfies
--
--   $$\int_G|\langle v,U_gv\rangle|^2dg=b_\mu=\frac1{d_\mu}.$$
--
--   Thus the inverse formal coefficient is the ordinary dimension in the compact normalized case.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 3, §III: formal dimension for compact G

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

/-- PDF p.3: compact probability-Haar formal dimension, including finite-dimensionality. -/
theorem compact_formal_dimension (hLie : RealLie G) [CompactSpace G] (i : M) :
    FiniteDimensional ℂ (D.I i i).range ∧ 0 < Module.finrank ℂ (D.I i i).range ∧
    formalCoefficient R D i = (Module.finrank ℂ (D.I i i).range : ℝ)⁻¹ ∧
    ∀ v : H, D.I i i v = v → ‖v‖ = 1 →
      (∫ g, ‖inner ℂ v (R.U g v)‖ ^ 2 ∂(R.dg)) =
        (Module.finrank ℂ (D.I i i).range : ℝ)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
