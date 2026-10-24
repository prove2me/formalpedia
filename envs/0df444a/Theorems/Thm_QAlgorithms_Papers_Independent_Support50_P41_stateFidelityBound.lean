-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_stateFidelityBound
-- name    : QAlgorithms.Papers.Independent.Support50.P41.stateFidelityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:16:19.529491+00:00
-- url     : https://prove2.me/theorems/2f6ce3cd-633a-4c2d-a3a6-9149405f7e03
-- title:
--   §4.3, equation (11): entanglement fidelity bounds input-output fidelity
-- statement:
--   For every density matrix $\rho$, CPTP map $\Phi$ on its nonzero finite-dimensional system, and normalized purification $\psi$ of $\rho$,
--
--   $$F_e(\psi,\Phi)\le F(\rho,\Phi(\rho)).$$
--
--   Here $F(\sigma,\tau)=(\operatorname{Tr}\sqrt{\sqrt\sigma\,\tau\sqrt\sigma})^2$ is squared mixed-state fidelity. This compares entanglement preservation with state preservation.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 16, §4.3, equation (11): entanglement fidelity bounds input-output fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- PDF p.16, (11): squared input-output fidelity bounds entanglement fidelity. -/
theorem stateFidelityBound {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi) :
    purificationFidelity psi Phi ≤ rootFidelity rho (Phi rho)^2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
