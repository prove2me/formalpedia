-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_operatorSumRepresentation
-- name    : QAlgorithms.Papers.Independent.Support50.P41.operatorSumRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:13:32.49972+00:00
-- url     : https://prove2.me/theorems/b160b862-4df3-4782-89e2-8378b65e2e99
-- title:
--   §2.2 theorem II; §A.2: normalized operator-sum representation
-- statement:
--   For a complex-linear completely positive trace-preserving map $\Phi$ on $M_d(\mathbb C)$, $d\ge1$, there are $m\le d^2$ matrices $A_\mu$ such that
--
--   $$\Phi(X)=\sum_\mu A_\mu X A_\mu^\dagger\quad\text{for every }X,\qquad \sum_\mu A_\mu^\dagger A_\mu=I_d.$$
--
--   The normalization is part of the representation theorem.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 6, §2.2 theorem II; §A.2: normalized operator-sum representation

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

/-- PDF pp.5--6,32--34, theorem II: normalized operator-sum representation from independent CP and TP. -/
theorem operatorSumRepresentation {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    ∃ m : ℕ, m ≤ d^2 ∧ ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      OperatorSum Phi A := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
