-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_weakComplementPhysical
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.weakComplementPhysical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:01:33.39636+00:00
-- url     : https://prove2.me/theorems/2f548b0d-a048-4a9f-a302-c90169f6fa86
-- title:
--   Weak complement, purity, and constructed purification
-- statement:
--   A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. For arbitrary complete system and environment Hilbert spaces (with a nonzero input space), both $E$ and $F$ are CPTP. If $\sigma$ is pure, $(E,F)$ is a true complementary pair. There exist a unit vector $v\in\mathcal H_B\otimes\ell^2(\mathbb N)$ purifying $\sigma$ and the isometry $V\psi=(U\otimes I)(\psi\otimes v)$. Writing $F_V$ for the ordinary complement of this same isometry,
--
--   $$E_V=E,\qquad \sigma=\operatorname{Tr}_C|v\rangle\langle v|,\qquad F=\operatorname{Tr}_C\circ F_V.$$
--
--   The purifying partial trace is CPTP. This identifies a weak complement as a marginal of the constructed ordinary complement, including mixed environments.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 4, Definition 1; (1.1)–(1.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Definition 1 and (1.3), PDF pp.3-4: CPTP weak complement, the pure case,
and the explicitly constructed purification U tensor identity. -/
theorem weakComplementPhysical {I J : Type} [Nonempty I]
    (U : Hilbert (I × J) ≃ₗᵢ[ℂ] Hilbert (I × J)) (sigma : State J) :
    IsTraceClassChannel (dilationReceiver U sigma.coefficients) ∧
    IsTraceClassChannel (weakComplement U sigma.coefficients) ∧
    (PureDensity sigma.coefficients →
      TrueComplementary (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients)) ∧
    ∃ (v : Hilbert (J × ℕ))
      (V : Hilbert I →ₗᵢ[ℂ] Hilbert (I × (J × ℕ))),
      ‖v‖ = 1 ∧ partialRight (rankOne v) = sigma.coefficients ∧
      PurifiedImplementation U v V ∧
      (∀ rho : State I, pureReceiver V rho.coefficients =
        dilationReceiver U sigma.coefficients rho.coefficients) ∧
      IsTraceClassChannel (fun X : Matrix (J × ℕ) (J × ℕ) ℂ => partialRight X) ∧
      TrueComplementary (dilationReceiver U sigma.coefficients) (pureComplement V) ∧
      (∀ rho : State I,
        weakComplement U sigma.coefficients rho.coefficients =
          partialRight (pureComplement V rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
