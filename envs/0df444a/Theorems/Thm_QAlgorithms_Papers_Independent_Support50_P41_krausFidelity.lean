-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_krausFidelity
-- name    : QAlgorithms.Papers.Independent.Support50.P41.krausFidelity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:15:23.184241+00:00
-- url     : https://prove2.me/theorems/8f39234b-069d-46ec-8e80-454d32194e1b
-- title:
--   §4.2, equation (10): intrinsic Kraus formula
-- statement:
--   Let $\rho$ be a density matrix on a nonzero finite-dimensional system, $\psi$ any normalized purification, and $\Phi(X)=\sum_\mu A_\mu X A_\mu^\dagger$ a fixed normalized operator-sum representation. Then
--
--   $$F_e(\psi,\Phi)=\sum_\mu|\operatorname{Tr}(\rho A_\mu)|^2.$$
--
--   This expresses fidelity intrinsically and gives the same value for every normalized Kraus representation.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 15, §4.2, equation (10): intrinsic Kraus formula

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

/-- PDF p.15, (10): scalar trace conjugation in the intrinsic Kraus formula. -/
theorem krausFidelity {d a m : ℕ} [NeZero d]
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (Phi : Superop (Fin d) (Fin d)) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : OperatorSum Phi A) :
    purificationFidelity psi Phi = ∑ k, Complex.normSq ((rho * A k).trace) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
