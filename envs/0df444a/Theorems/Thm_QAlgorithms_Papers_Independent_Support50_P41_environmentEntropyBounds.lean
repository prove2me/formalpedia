-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_environmentEntropyBounds
-- name    : QAlgorithms.Papers.Independent.Support50.P41.environmentEntropyBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:29:03.616171+00:00
-- url     : https://prove2.me/theorems/ad8fbf64-a3f5-4694-8c2b-b58f44cc47f5
-- title:
--   §5.2, equations (18)–(19) and absolute-value summary
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices of a nonzero finite system and environment, initially in the product state $\rho\otimes\sigma$. A fixed unitary $U$ induces $\Phi(X)=\operatorname{Tr}_E[U(X\otimes\sigma)U^\dagger]$ and final environment state $\sigma'=\operatorname{Tr}_Q[U(\rho\otimes\sigma)U^\dagger]$. Then
--
--   $$|S(\sigma')-S(\sigma)|\le S_e(\rho,\Phi)\le S(\sigma)+S(\sigma').$$
--
--   This bounds both directions of environment entropy change even when its initial state is mixed.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 23, §5.2, equations (18)–(19) and absolute-value summary

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

/-- PDF pp.23--24, (18)--(19): arbitrary mixed environment with product initialization. -/
theorem environmentEntropyBounds {d e : ℕ} [NeZero d] [NeZero e]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (sigma : Matrix (Fin e) (Fin e) ℂ) (hsigma : IsDensityMatrix sigma)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    let Phi := fun X => traceRight (mixedInteraction U sigma X)
    let sigmaOut := traceLeft (mixedInteraction U sigma rho)
    |vnEntropy sigmaOut - vnEntropy sigma| ≤ entropyExchange Phi rho ∧
    entropyExchange Phi rho ≤ vnEntropy sigma + vnEntropy sigmaOut := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
