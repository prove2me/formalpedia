-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_cpKrausBound
-- name    : QAlgorithms.Papers.Independent.Support50.P41.cpKrausBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:34:18.214529+00:00
-- url     : https://prove2.me/theorems/e765e97e-f809-4670-8729-70637ea4c7d7
-- title:
--   §A.2: at most d squared Kraus terms for a CP map
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be any complex-linear completely positive map, with $d\ge1$. There are $m\le d^2$ matrices $A_\mu$ such that
--
--   $$\Phi(X)=\sum_{\mu=1}^{m}A_\mu X A_\mu^\dagger\qquad\text{for every }X.$$
--
--   Trace preservation and Kraus normalization are not required; the zero map is included. This is the broader CP representation statement in the appendix.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 34, §A.2: at most d squared Kraus terms for a CP map

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

/-- PDF p.34: at most d squared Kraus terms for CP maps, without TP or nonzero-map hypotheses. -/
theorem cpKrausBound {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    ∃ m : ℕ, m ≤ d^2 ∧ ∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ,
      ∀ X, Phi X = krausApply A X := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
