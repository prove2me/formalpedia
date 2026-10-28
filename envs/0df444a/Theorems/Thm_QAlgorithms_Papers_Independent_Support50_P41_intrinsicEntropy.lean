-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_intrinsicEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.intrinsicEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:20:30.435504+00:00
-- url     : https://prove2.me/theorems/575b512c-5fa3-493c-b1a4-153ba2972a50
-- title:
--   §5.1, equation (12): purification independence of entropy production
-- statement:
--   Fix a density matrix $\rho$ and CPTP map $\Phi$ on a nonzero finite-dimensional system. Any normalized purifications $\psi$ and $\phi$ of $\rho$, with arbitrary finite reference dimensions, satisfy
--
--   $$S((\mathrm{id}\otimes\Phi)(|\psi\rangle\langle\psi|))=S_e(\rho,\Phi)=S((\mathrm{id}\otimes\Phi)(|\phi\rangle\langle\phi|)).$$
--
--   Entropy is in bits. This makes the definition of entropy production independent of the chosen purification.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 19, §5.1, equation (12): purification independence of entropy production

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

/-- PDF pp.19--20, (12): entropy production is independent of reference and purification. -/
theorem intrinsicEntropy {d a b : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (phi : EuclideanSpace ℂ (Fin b × Fin d)) (hphi : IsPurification rho phi) :
    vnEntropy (idTensorSuperop Phi (pureDensity psi)) = entropyExchange Phi rho ∧
    vnEntropy (idTensorSuperop Phi (pureDensity phi)) = entropyExchange Phi rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
