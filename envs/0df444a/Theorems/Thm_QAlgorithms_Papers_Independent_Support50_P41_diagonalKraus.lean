-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_diagonalKraus
-- name    : QAlgorithms.Papers.Independent.Support50.P41.diagonalKraus
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:23:30.595597+00:00
-- url     : https://prove2.me/theorems/cc45d724-3c7c-4e76-9795-5bf96b961c40
-- title:
--   §5.1: diagonal operator-sum representation for a specified input
-- statement:
--   For every density matrix $\rho$ and CPTP map $\Phi$ on a nonzero finite-dimensional system, there exists a normalized Kraus representation $(A_\mu)$ with
--
--   $$\operatorname{Tr}(A_\mu\rho A_\nu^\dagger)=0\quad(\mu\ne\nu).$$
--
--   Thus the exchange matrix can be diagonalized by choosing the representation. No full-rank assumption on $\rho$ or global minimality is asserted.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 21, §5.1: diagonal operator-sum representation for a specified input

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

/-- PDF p.21: existence of an input-dependent diagonal representation; no minimality for singular inputs. -/
theorem diagonalKraus {d : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ m : ℕ, ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A ∧ ∀ k l, k ≠ l → (A k * rho * (A l)ᴴ).trace = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
