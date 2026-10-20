-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P25_covariant_teleportation_simulation
-- name    : QAlgorithms.Papers.Independent.Frontier30.P25.covariant_teleportation_simulation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:39:09.507977+00:00
-- url     : https://prove2.me/theorems/3337a3eb-d67f-4f2f-a7f9-bc80896bcfb5
-- title:
--   Covariant channels admit a fixed Choi-state teleportation simulation
-- statement:
--   Let $\mathcal N:\mathcal L(I)\to\mathcal L(B)$ be a finite-dimensional CPTP map, with nonzero input and output dimensions. Let a finite group $G$ have unitary representations $U$ on $I$ and $V$ on $B$ satisfying $\mathcal N(U_g\rho U_g^\dagger)=V_g\mathcal N(\rho)V_g^\dagger$ for every density operator $\rho$. Assume $U$ is a unitary one-design: its average conjugation sends every density operator to $I_I/d$, where $d=\dim I$.
--
--   There is one fixed teleportation protocol, using the state $\omega_{IB}=(\mathrm{id}_I\otimes\mathcal N)(\Phi_{II})$, that realizes
--
--   $$\mathcal T(\rho\otimes\omega)=\mathcal N(\rho)\qquad\text{for every density operator }\rho.$$
--
--   Here $\Phi$ is the normalized maximally entangled projector. Specifically, Alice uses the POVM $M_g=(d^2/|G|)(U_g\otimes I)\Phi(U_g^\dagger\otimes I)$, sends $g$, and Bob applies $V_g$. All resources and operations precede the input quantifier. This gives an explicit channel simulation usable within larger protocols.
-- source:
--   Converse bounds for private communication over quantum channels, arXiv:1602.08898v3, PDF p. 7, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P25

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Pinned accepted definitions; assessments record the domains of equivalence.

open QAlgorithms.Papers.Independent.Dependency50.P09 (OneDesign relativeD sandwichedD)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits idealCCQ)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity privateState privacyTest)

/-- PDF p.7, Proposition 2; explicit fixed simulation from Appendix A, pp.35–36.
The resource is the computed Choi state, and the simulation works for every input. -/
theorem covariant_teleportation_simulation
    {G I B : Type} [Fintype G] [Group G] [Fintype I] [Nonempty I]
    [Fintype B] [Nonempty B] (N : Superop I B) (hN : IsChannel N)
    (U : G →* Matrix.unitaryGroup I ℂ) (V : G →* Matrix.unitaryGroup B ℂ)
    (hcov : Covariant N U V) (hdesign : OneDesign U) :
    ∃ M : G → Matrix (I × I) (I × I) ℂ,
      M = bellPOVM U ∧ IsPOVM M ∧
      ∀ rho : Matrix I I ℂ, IsDensityMatrix rho →
        teleportOutput M V (idTensorSuperop (R := I) N (pureDensity (bell I))) rho = N rho := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P25

end
