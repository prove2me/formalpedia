-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_coherentInformation_additivity
-- name    : QAlgorithms.Papers.Independent.Support50.P01.coherentInformation_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:07:50.177407+00:00
-- url     : https://prove2.me/theorems/444da655-3e07-4c0f-b6e4-de39879c51d4
-- title:
--   §II.C: coherent-information subadditivity and additivity
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. If $\mathcal N$ is conjugate degradable, every two-use density operator $\rho_{A_1A_2}$, with actual partial-trace marginals $\rho_{A_i}$, satisfies
--   $$
--   I_c(\mathcal N^{\otimes2},\rho_{A_1A_2})\le I_c(\mathcal N,\rho_{A_1})+I_c(\mathcal N,\rho_{A_2}),\qquad
--   Q^{(1)}(\mathcal N^{\otimes n})=nQ^{(1)}(\mathcal N)\quad(n\ge1).
--   $$
--   The first assertion retains entangled inputs, and the second gives optimized additivity.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 4, §II.C: coherent-information subadditivity and additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.4: subadditivity on arbitrary two-use inputs and optimized n-use additivity. -/
theorem coherentInformation_additivity (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : ConjugateDegradable U) :
    (∀ rho : Matrix (Fin 2 → Fin a) (Fin 2 → Fin a) ℂ, IsDensityMatrix rho →
      blockCoherentInformation U 2 rho ≤
        coherentInformation (receiverChannel U) (fun x y => ∑ t : Fin a, rho ![x,t] ![y,t]) +
        coherentInformation (receiverChannel U) (fun x y => ∑ t : Fin a, rho ![t,x] ![t,y])) ∧
    ∀ n : ℕ, 0<n → maximumCoherentInformation (dilationPower U n) = (n : ℝ) * maximumCoherentInformation U := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
