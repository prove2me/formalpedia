-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_systemEntropyBounds
-- name    : QAlgorithms.Papers.Independent.Support50.P41.systemEntropyBounds
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:28:20.546184+00:00
-- url     : https://prove2.me/theorems/774ec777-bac8-4717-8545-4713f6f1c74e
-- title:
--   §5.2, equations (16)–(17) and absolute-value summary
-- statement:
--   For a density matrix $\rho$ and CPTP map $\Phi$ on a nonzero finite-dimensional system, write $\rho'=\Phi(\rho)$. Then
--
--   $$|S(\rho')-S(\rho)|\le S_e(\rho,\Phi)\le S(\rho)+S(\rho').$$
--
--   All entropies are in bits. The lower bound covers entropy decrease as well as increase.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 24, §5.2, equations (16)–(17) and absolute-value summary

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

/-- PDF pp.23--24, (16)--(17) and summary: both signs of system entropy change are bounded. -/
theorem systemEntropyBounds {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    |vnEntropy (Phi rho) - vnEntropy rho| ≤ entropyExchange Phi rho ∧
    entropyExchange Phi rho ≤ vnEntropy rho + vnEntropy (Phi rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
