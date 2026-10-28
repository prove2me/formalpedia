-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_unitaryReferenceEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.unitaryReferenceEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:26:56.825764+00:00
-- url     : https://prove2.me/theorems/da47ea58-be21-4648-8a69-1cec033e8279
-- title:
--   §5.1 parenthetical extension: arbitrary isolated-reference unitary
-- statement:
--   Let $\psi$ be a normalized purification of a density matrix $\rho$, let $\Phi$ be CPTP on its nonzero finite-dimensional system, and let $U_R$ be any unitary on the isolated finite reference. Set $\rho'_{RQ}=(\mathrm{id}_R\otimes\Phi)(|\psi\rangle\langle\psi|)$. Then
--
--   $$S((U_R\otimes I)\rho'_{RQ}(U_R^\dagger\otimes I))=S_e(\rho,\Phi).$$
--
--   This extends the entropy interpretation to a reference with internal unitary evolution.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 22, §5.1 parenthetical extension: arbitrary isolated-reference unitary

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

/-- PDF p.22, parenthetical extension: arbitrary isolated-reference unitary preserves the entropy statement. -/
theorem unitaryReferenceEntropy {d a : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (U : Matrix.unitaryGroup (Fin a) ℂ) :
    vnEntropy (conjSuperop (Matrix.kronecker (U : Matrix (Fin a) (Fin a) ℂ)
      (1 : Matrix (Fin d) (Fin d) ℂ)) (idTensorSuperop Phi (pureDensity psi))) =
      entropyExchange Phi rho := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
