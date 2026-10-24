-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P41_krausUnitaryFreedom
-- name    : QAlgorithms.Papers.Independent.Support50.P41.krausUnitaryFreedom
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T22:37:45.065882+00:00
-- url     : https://prove2.me/theorems/5b633429-67b2-460e-aae4-5bb59a71d565
-- title:
--   §A.4: unitary mixing of two operator-sum representations
-- statement:
--   Let $(A_\mu)_{\mu<m}$ and $(B_\nu)_{\nu<n}$ be normalized operator-sum representations of the same channel on a nonzero finite-dimensional system. Append zero operators to both lists to obtain length $L=\max(m,n)$. There exists a unitary $L\times L$ matrix $U$ with
--
--   $$A_\mu=\sum_{\nu<L}U_{\mu\nu}B_\nu\qquad(\mu<L).$$
--
--   The unitary acts on representation labels and has the printed orientation without an extra complex conjugation.
-- source:
--   Sending quantum entanglement through noisy channels, arXiv:quant-ph/9604023v1, PDF p. 37, §A.4: unitary mixing of two operator-sum representations

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

/-- PDF pp.36--37: zero padding and printed orientation of the unitary mixing of Kraus labels. -/
theorem krausUnitaryFreedom {d m n : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : OperatorSum Phi A)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (hB : OperatorSum Phi B) :
    ∃ U : Matrix.unitaryGroup (Fin (max m n)) ℂ,
      ∀ k : Fin (max m n), padKraus A (max m n) k =
        ∑ l, (U : Matrix (Fin (max m n)) (Fin (max m n)) ℂ) k l •
          padKraus B (max m n) l := by sorry

end QAlgorithms.Papers.Independent.Support50.P41

end
