-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_stabilizer_average
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.stabilizer_average
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:07:30.81467+00:00
-- url     : https://prove2.me/theorems/c9907bec-0261-4757-a3ec-44e3a63a0aec
-- title:
--   §IV, Eq.(13): stabilizer averaging preserves the objective
-- statement:
--   Let $\psi$ be a unit vector under the unimodular Lie-group action $U$, let $K$ be its actual compact ray stabilizer, and let $dk$ be probability Haar measure on $K$. If $\Xi$ is a positive bounded operator with weak group average $I$, its weak stabilizer average exists and satisfies
--
--   $$\overline\Xi=\int_K U_k\Xi U_k^\dagger dk,\qquad\langle\psi,\overline\Xi\psi\rangle=\langle\psi,\Xi\psi\rangle.$$
--
--   The averaged seed is positive, remains normalized on $G$, and commutes with $K$, so it descends to the coset orbit. The trace objective is also preserved for every density operator fixed by $K$, including an invariant-goal transformed state. Any attained universal bound is therefore preserved.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 4, §IV, Eq.(13): stabilizer averaging preserves the objective

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

/-- PDF p.4, Eq.(13): stabilizer averaging preserves feasibility and both objectives.
The mixed-state clause applies to any state fixed by K, including the invariant-goal transform. -/
theorem stabilizer_average (hLie : RealLie G) (psi : H) (hn : ‖psi‖ = 1)
    (K : Subgroup G) (hK : RayStabilizer R psi K) (S : StabilizerHaar K)
    (A : PhysicalOperator H) (hA : ContinuousLinearMap.IsPositive A) (hN : WeaklyNormalizedSeed R A) :
    WeakIntegral S.dh (fun k : K => conjugatedSeed R A k) (stabilize R S A) ∧
    Seed R K (stabilize R S A) ∧ pureSeedDensity (stabilize R S A) psi = pureSeedDensity A psi ∧
    (∀ rho : PhysicalOperator H, HilbertDensity rho → (∀ k : K, conjugatedSeed R rho k = rho) →
      mixedLikelihood (stabilize R S A) rho = mixedLikelihood A rho) ∧
    (∀ L, (∀ B, Seed R K B → pureSeedDensity B psi ≤ L) → pureSeedDensity A psi = L →
      Maximum R K psi (stabilize R S A) L) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
