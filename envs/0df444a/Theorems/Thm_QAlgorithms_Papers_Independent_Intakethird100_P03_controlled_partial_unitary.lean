-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_controlled_partial_unitary
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.controlled_partial_unitary
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:56:50.404393+00:00
-- url     : https://prove2.me/theorems/df30c8ec-7109-4fa5-8137-0e8a4628803b
-- title:
--   Lemma 6: one-call controlled U when U fixes zero
-- statement:
--   For every $n$, a fixed sequence over $Q$ and one plain partial-unitary oracle call implements controlled $U$ whenever $U:N\to M$ contains and fixes the computational zero state. It uses clean work and satisfies
--
--   $$
--   \operatorname{length}=4n+1,\qquad\#U=1.
--   $$
--
--   On the valid controlled domain $|0\rangle N\oplus|1\rangle N$, it maps $|0\rangle\xi$ to itself and $|1\rangle\xi$ to $|1\rangle U\xi$, returning work exactly to zero on every superposition. Its range is $|0\rangle N\oplus|1\rangle M$. Every partial oracle call is defined on its incoming vector.
--
--   The sequence is chosen before the oracle, with no free controlled or inverse call.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 13, Lemma 6: one-call controlled U when U fixes zero

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.13, Lemma 6: one plain U call and four controlled-XOR sweeps (4n Toffolis).
U fixes zero exactly; all work is clean on the whole valid controlled subspace. The gate
list is chosen before the oracle, and every partial call is checked on its actual input. -/
theorem controlled_partial_unitary (n : ℕ) :
    ∃ (w : ℕ) (c : List (PartialOracleStep n ((n + 1) + w))),
      c.length = 4 * n + 1 ∧ partialOracleCount c = 1 ∧
      ∀ (U : PartialUnitary (Qubits n)) (hzero : zeroKet n ∈ U.domain),
        (U.iso ⟨zeroKet n, hzero⟩ : EuclideanSpace ℂ (Qubits n)) = zeroKet n →
        ∀ v : EuclideanSpace ℂ (Qubits (n + 1)), ControlledDomain U v →
          ValidPartialExecution c U (cleanVector w v) ∧
          act (partialOracleMatrix c U) (cleanVector w v) =
            cleanVector w (act (controlledQubits U.matrix) v) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
