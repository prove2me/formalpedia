-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_pureInputFidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P41.pureInputFidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:17:29.404722+00:00
-- url     : https://prove2.me/theorems/dcdd510f-12da-4b43-bc90-ffc19ab9c133
-- title:
--   §4.3: equality for a pure input
-- statement:
--   Let $v$ be a unit vector on a nonzero finite-dimensional system, $\rho=|v\rangle\langle v|$, and $\Phi$ any CPTP map. For every normalized purification $\psi$ of $\rho$,
--
--   $$F_e(\psi,\Phi)=F(\rho,\Phi(\rho)),$$
--
--   where $F$ denotes squared mixed-state fidelity. Thus the two notions coincide for pure input.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 17, §4.3: equality for a pure input

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

/-- PDF pp.16--17: equality of squared fidelities for a pure input. -/
theorem pureInputFidelity {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification (pureDensity v) psi) :
    purificationFidelity psi Phi = rootFidelity (pureDensity v) (Phi (pureDensity v))^2 := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
