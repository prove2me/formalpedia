-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_environmentEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.environmentEntropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:25:31.351136+00:00
-- url     : https://prove2.me/theorems/f49a45a1-1c15-41c4-8f54-c75c0060aa07
-- title:
--   §5.1: entropy exchange equals pure-environment output entropy
-- statement:
--   Let $\rho$ be a density matrix, $\eta$ a unit vector of a finite environment initially independent of the system, and $U$ a unitary on system and environment. Write $\Phi(X)=\operatorname{Tr}_E U(X\otimes|\eta\rangle\langle\eta|)U^\dagger$ and $\rho'_E=\operatorname{Tr}_Q U(\rho\otimes|\eta\rangle\langle\eta|)U^\dagger$. Then
--
--   $$S_e(\rho,\Phi)=S(\rho'_E).$$
--
--   All entropies are in bits. The environment dimension need not be minimal.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 22, §5.1: entropy exchange equals pure-environment output entropy

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

/-- PDF p.22: entropy exchange equals output entropy of an independent initially pure environment. -/
theorem environmentEntropy {d e : ℕ} [NeZero d] [NeZero e]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (heta : IsState eta)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    entropyExchange (dilationChannel U eta) rho = vnEntropy (environmentOutput U eta rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
