-- Prove2me | Theorems.Thm_QuantumHMMR_lemma_4_1
-- name    : QuantumHMMR.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:57.131192+00:00
-- url     : https://prove2.me/theorems/fdbef554-05c2-4b9e-a20d-46f4b15f384a
-- title:
--   Lemma 4.1 — acceptance probabilities are linear in the moment operator
-- statement:
--   Let $t \in \mathbb N$ and let $A^U$ be any adaptive $t$-query algorithm with forward access to an $n$-qubit unitary $U$, followed by a two-outcome measurement $(M_A, I - M_A)$. Let $d = 2^n$. Then there exists a matrix $\Lambda_A$, depending only on the algorithm and its measurement, such that for every unitary ensemble $\nu$
--   $$
--   \mathop{\mathbb E}_{U\sim\nu} \mathrm{Tr}\big[M_A |A^U_t\rangle\langle A^U_t|\big] = \mathrm{Tr}\big[\Lambda_A^\dagger M^{(t)}_\nu\big], \qquad \|\Lambda_A\|_1 \le d^{2t}. \tag{11}
--   $$
--
--   The lemma turns every distinguishing experiment into a linear functional of bounded trace norm on moment operators; spectral bounds on moment operators then bound the advantage of every algorithm at once.
--
--   Differences from the source:
--   - encoding: every unitary ensemble ν → every probability measure on n-qubit matrices almost surely supported on unitaries; reason: the same objects
--   - encoding: two-outcome measurement (M_A, I − M_A) → an effect 0 ⪯ M ⪯ I (published IsEffect); reason: the same objects
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Lemma 4.1, Eq. (11), p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QuantumHMMR_AdaptiveAlg
import Definitions.Def_QuantumHMMR_IsAcceptanceMatrix

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- **Lemma 4.1** (acceptance probabilities from moment operators; Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), Eq. (11), p.12).
Let `t ∈ ℕ` and let `A^U` be an adaptive `t`-query algorithm with forward access to an `n`-qubit
unitary, followed by a two-outcome measurement `(M_A, I - M_A)`; let `d = 2ⁿ`. There is a matrix
`Λ_A`, depending only on the algorithm and its measurement, such that for **every** unitary
ensemble `ν`, `E_{U∼ν} Tr[M_A |A^U_t⟩⟨A^U_t|] = Tr[Λ_A† M^{(t)}_ν]`, and `‖Λ_A‖₁ ≤ d^{2t}`.

**Formalization Note** One `Λ` is chosen before the ensemble (`IsAcceptanceMatrix` quantifies over
every probability measure almost surely supported on unitaries). `‖·‖₁` is the published
`traceNorm`; `Λ` is indexed like `U^{⊗t} ⊗ Ū^{⊗t}`. `t = 0` is allowed. -/
theorem lemma_4_1 (n t : ℕ) (alg : AdaptiveAlg n t)
    (M : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) (hM : IsEffect M) :
    ∃ Λ : Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
        ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
      IsAcceptanceMatrix alg M Λ ∧ traceNorm Λ ≤ ((2 : ℝ) ^ n) ^ (2 * t) := by sorry

end QuantumHMMR
