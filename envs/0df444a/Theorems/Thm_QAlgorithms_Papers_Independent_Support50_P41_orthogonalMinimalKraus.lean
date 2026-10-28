-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_orthogonalMinimalKraus
-- name    : QAlgorithms.Papers.Independent.Support50.P41.orthogonalMinimalKraus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:24:21.586988+00:00
-- url     : https://prove2.me/theorems/be16370a-6692-4e45-b532-bf0ff6650f21
-- title:
--   §5.1: minimal orthogonal representation at maximally mixed input
-- statement:
--   Every CPTP map $\Phi$ on a nonzero finite-dimensional system has a normalized Kraus representation $(A_\mu)$ of nonzero Hilbert--Schmidt orthogonal operators. Furthermore, every such representation is minimal:
--
--   $$\operatorname{Tr}(A_\mu^\dagger A_\nu)=0\ (\mu\ne\nu),\ A_\mu\ne0
--   \quad\Longrightarrow\quad m\le n$$
--
--   for every other Kraus representation with $n$ terms, where $m$ is the size of $(A_\mu)$. These are the diagonal representations at maximally mixed input after discarding zero operators.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 21, §5.1: minimal orthogonal representation at maximally mixed input

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

/-- PDF p.21: a nonzero orthogonal Kraus family exists and is minimal; read in the maximally mixed case. -/
theorem orthogonalMinimalKraus {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi) :
    (∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ (∀ k, A k ≠ 0) ∧
        ∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0) ∧
    ∀ m (A : Fin m → Matrix (Fin d) (Fin d) ℂ), OperatorSum Phi A →
      (∀ k, A k ≠ 0) → (∀ k l, k ≠ l → ((A k)ᴴ * A l).trace = 0) →
      ∀ n (B : Fin n → Matrix (Fin d) (Fin d) ℂ), OperatorSum Phi B → m ≤ n := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
