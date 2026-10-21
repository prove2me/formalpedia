-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_canonical_finite_components
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.canonical_finite_components
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:10:52.596869+00:00
-- url     : https://prove2.me/theorems/2327583c-48f1-489c-8ce5-b83afb85f1bd
-- title:
--   §IV, Eqs.(16)–(18): canonical optimum with finitely many irreducible components
-- statement:
--   Let a unit vector $\psi$ be acted on by a strongly continuous projective unitary representation of a unimodular Lie group. Assume a finite complete orthogonal family of nonzero square-integrable irreducible components and a compact ray stabilizer $K$. A new decomposition can be chosen within the same isotypic blocks so that distinct equivalent occupied unit components $\psi_\mu$ satisfy $\langle\psi_\mu,I_{\mu\nu}\psi_\nu\rangle=0$. Absorb each coefficient phase into its unit component and write $c_\mu=\|P_\mu\psi\|$. With $b_\mu$ the formal coefficients, define
--
--   $$\eta=\sum_{c_\mu>0}\sqrt{b_\mu^{-1}}\,\psi_\mu,\qquad\Xi_0=|\eta\rangle\langle\eta|+\sum_{c_\nu=0}b_\nu^{-1}|\phi_\nu\rangle\langle\phi_\nu|,$$
--
--   where each $\phi_\nu$ is a unit vector in its absent component. The probability-Haar average of $\Xi_0$ over $K$ is a positive normalized quotient-covariant seed and attains, against every competing normalized seed,
--
--   $$L_{\max}=\left(\sum_\mu c_\mu\sqrt{b_\mu^{-1}}\right)^2.$$
--
--   Component spaces may be infinite dimensional; the finite component count makes this a bounded-operator construction.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 4, §IV, Eqs.(16)–(18): canonical optimum with finitely many irreducible components

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

/-- PDF pp.4–5, Eqs.(16)–(18), Appendix pp.7–8: adapted decomposition exists;
the full canonical seed, after the actual stabilizer average, attains the sharp bound.
This separately identified finite-component consequence includes infinite-dimensional irreps. -/
theorem canonical_finite_components [Fintype M] (hLie : RealLie G) (psi : H)
    (hn : ‖psi‖ = 1) (K : Subgroup G) (hK : RayStabilizer R psi K)
    (S : StabilizerHaar K) :
    ∃ E : Components R M, SameIsotypic R D E ∧ Adapted R E psi ∧
      WeakIntegral S.dh (fun k : K => conjugatedSeed R (canonicalSeed R E psi) k)
        (stabilize R S (canonicalSeed R E psi)) ∧
      Maximum R K psi (stabilize R S (canonicalSeed R E psi))
        ((∑ i, ‖E.I i i psi‖ * Real.sqrt ((formalCoefficient R E i)⁻¹)) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
