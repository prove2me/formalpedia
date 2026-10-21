-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_optimal_input_states
-- name    : QAlgorithms.Papers.Independent.Next46.P39.optimal_input_states
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:43:51.298993+00:00
-- url     : https://prove2.me/theorems/559c3293-fa8e-49d7-b870-5357922bd6c4
-- title:
--   Optimal input states and the likelihood ceiling
-- statement:
--   Let $U$ be the specified continuous projective unitary action of a compact Lie group on a nonzero finite-dimensional complex Hilbert space. Fix a complete isotypic decomposition with inequivalent irreducible dimensions $d_\mu>0$ and multiplicities $m_\mu>0$, and probability Haar measure $dg$. Put $k_\mu=\min(d_\mu,m_\mu)$ and $L=\sum_\mu d_\mu k_\mu$. Every density matrix and every normalized measurable integrable POVM density have uniform-prior average likelihood at most $L$. In particular every normalized covariant seed has constant diagonal likelihood at most $L$.
--
--   $$p_{\mathrm{av}}\le L=\sum_\mu d_\mu\min(d_\mu,m_\mu).$$
--
--   Normalized pure inputs with arbitrary sector phases, maximally entangled sector vectors of Schmidt rank $k_\mu$, and sector probabilities $d_\mu k_\mu/L$ exist; every such input attains $L$ with a normalized full-space covariant measurement. This identifies the exact optimal likelihood density, which for a finite group must be divided by its order to obtain success probability.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 10, Theorem 3 (optimal input states), Eqs.(24)–(25); capstone selected from the p.1 abstract

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

/-- PDF p.10, Theorem 3, Eqs.(24)–(25). The proof's printed `max` is corrected
to `min`, as required by the theorem and the Schmidt-rank bound on p.7.
For arbitrary measurements the bound is uniform-prior average likelihood;
for covariant measurements it is the constant diagonal likelihood. -/
theorem optimal_input_states (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G) (R : FiniteModel G I S) :
    (∀ (rho : Matrix I I ℂ), QAlgorithms.IsDensityMatrix rho →
      (∀ M : DensityPOVM I G, M.reference = R.dg →
        Integrable (fun g => QAlgorithms.effectProb (M.density g) (densityOrbit R rho g)) R.dg ∧
          averageLikelihood R M rho ≤ ceilingLikelihood R) ∧
      (∀ Xi, IsSeed R Xi → likelihood Xi rho ≤ ceilingLikelihood R)) ∧
    (∃ D : SchmidtInput R, D.OptimalShape) ∧
    (∀ D : SchmidtInput R, D.OptimalShape →
      QAlgorithms.IsState D.vector ∧ ∃ Xi, IsSeed R Xi ∧
        likelihood Xi (QAlgorithms.pureDensity D.vector) = ceilingLikelihood R) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
