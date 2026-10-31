-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_cptp_contractivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.cptp_contractivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:39:44.873534+00:00
-- url     : https://prove2.me/theorems/333414e7-e8b2-4fba-b433-7d15b3a2310d
-- title:
--   Theorem 1: CPTP contractivity
-- statement:
--   All registers are finite and nonempty; all input density matrices are positive semidefinite with trace one.
--
--   Let $D$ be one coherent extended-real distance family on all finite register dimensions and on positive subnormalized blocks, including zero. Assume unitary invariance on normalized states (F2), partial-trace contractivity on normalized states (F3), and invariance under adjoining a rank-one projector onto a unit vector (proof-used F5b). For any CPTP map $\Phi$ and density matrices $\sigma,\rho$,
--
--   $$D(\Phi(\sigma)\Vert\Phi(\rho))\le D(\sigma\Vert\rho).$$
--
--   No locality is required. This is deterministic contractivity under the three stated conditions.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 9, Theorem 1: CPTP contractivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 1, PDF p.9 (introduced p.8): CPTP contractivity under F2,F3,F5b only. -/
theorem cptp_contractivity (D : DistanceFamily) (h2 : UnitaryInvariantDistance D) (h3 : F3 D) (h5 : F5b D)
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] (Phi : Superop I J) (hPhi : IsChannel Phi)
    (sigma rho : Matrix I I ℂ) (hsigma : IsDensityMatrix sigma) (hrho : IsDensityMatrix rho) :
    D (Phi sigma) (Phi rho) ≤ D sigma rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
