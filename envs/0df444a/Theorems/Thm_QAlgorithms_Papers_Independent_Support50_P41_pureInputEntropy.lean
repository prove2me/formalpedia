-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_pureInputEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.pureInputEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:26:14.115077+00:00
-- url     : https://prove2.me/theorems/0ea6a9ea-5f18-4ce3-8563-0f93f1616edd
-- title:
--   §5.1: pure input gives output entropy
-- statement:
--   Let $v$ be a unit vector on a nonzero finite-dimensional system and $\Phi$ a CPTP map. For the pure input $\rho=|v\rangle\langle v|$,
--
--   $$S_e(\rho,\Phi)=S(\Phi(\rho)).$$
--
--   Thus entropy production equals system output entropy in the pure-input case. Entropies use base two.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 22, §5.1: pure input gives output entropy

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

/-- PDF p.22: pure input gives entropy production equal to output entropy. -/
theorem pureInputEntropy {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    entropyExchange Phi (pureDensity v) = vnEntropy (Phi (pureDensity v)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
