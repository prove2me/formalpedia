-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_discrete_canonical
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.discrete_canonical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:12:00.093802+00:00
-- url     : https://prove2.me/theorems/bebadcd5-03fa-4b49-8114-1269ced305d2
-- title:
--   §IV: discrete-group version
-- statement:
--   Let $G$ be a discrete unimodular group with a projective unitary action on a complete complex Hilbert space, a finite complete family of square-summable irreducible components, and a unit input $\psi$ with finite ray stabilizer. Keep the chosen two-sided Haar scale; for finite $G$ it has mass one. The state-adapted decomposition, full canonical completion, and stabilizer averaging give a normalized positive covariant seed attaining
--
--   $$L_{\max}=\left(\sum_\mu\|P_\mu\psi\|\sqrt{b_\mu^{-1}}\right)^2,$$
--
--   and every competing normalized seed obeys this bound. Here $b_\mu$ is the same coefficient-square Haar integral, which becomes the appropriately scaled discrete sum. The result preserves the finite-component regime without assuming finite-dimensional components.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 5, §IV: discrete-group version

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

/-- PDF p.5: discrete version in the same finite-component regime. Haar scale is
retained, so a finite group uses the normalized sum required by §II. -/
theorem discrete_canonical [Fintype M] [DiscreteTopology G] (psi : H)
    (hn : ‖psi‖ = 1) (K : Subgroup G) (hK : RayStabilizer R psi K)
    (S : StabilizerHaar K) :
    ∃ E : Components R M, SameIsotypic R D E ∧ Adapted R E psi ∧
      WeakIntegral S.dh (fun k : K => conjugatedSeed R (canonicalSeed R E psi) k)
        (stabilize R S (canonicalSeed R E psi)) ∧
      Maximum R K psi (stabilize R S (canonicalSeed R E psi))
        ((∑ i, ‖E.I i i psi‖ * Real.sqrt ((formalCoefficient R E i)⁻¹)) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
