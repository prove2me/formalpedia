-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_exchangeMatrixEntropy
-- name    : QAlgorithms.Papers.Independent.Support50.P41.exchangeMatrixEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:21:31.57302+00:00
-- url     : https://prove2.me/theorems/093a4e6d-83ea-464a-b7a7-71a4c82c0529
-- title:
--   §5.1, equations (13)–(14): exchange-matrix entropy
-- statement:
--   Let $\rho$ be a density matrix and $(A_\mu)$ a normalized operator-sum representation of a channel $\Phi$. Construct
--
--   $$W_{\mu\nu}=\operatorname{Tr}(A_\mu\rho A_\nu^\dagger).$$
--
--   Then $W$ is a density matrix and $S_e(\rho,\Phi)=S(W)$, with entropy in bits. This computes entropy exchange using only the input and Kraus operators.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 21, §5.1, equations (13)–(14): exchange-matrix entropy

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

/-- PDF pp.20--21, (13)--(14): computed exchange matrix and its entropy, with the printed order.
Source correction: the first p.20 formula for rho_E prints Tr_E; use Tr_RQ,
as in the immediately following derivation. Independent moderation pending. -/
theorem exchangeMatrixEntropy {d m : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : OperatorSum Phi A)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ k l, complementaryMap A rho k l = (A k * rho * (A l)ᴴ).trace) ∧
    IsDensityMatrix (complementaryMap A rho) ∧
    entropyExchange Phi rho = vnEntropy (complementaryMap A rho) := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
