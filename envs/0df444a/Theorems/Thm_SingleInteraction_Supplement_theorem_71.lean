-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_71
-- name    : SingleInteraction.Supplement.theorem_71
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:12:06.193287+00:00
-- url     : https://prove2.me/theorems/d394daac-91d4-4dcb-af85-3bb2f1df38b6
-- title:
--   Theorem 71 — a uniform family $\{\hat h^{(n)}\}$ of 5-local interactions for which DSIH$_5$ is QMA-complete
-- statement:
--   There is a family $\{\hat h^{(n)}\}_{n\ge1}$ of 5-qubit Hermitian matrices, uniform in the sense of Definition 32, such that DSIH$_5$ with this family is QMA-complete: membership in QMA and QMA-hardness, for unweighted copies of $\hat h^{(n)}$ on pairwise distinct ordered 5-tuples of distinct qubits, $n$ the final number of physical qubits.
--
--   This removes the pinning resource of Theorem 69 at the cost of two more qubits of locality.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 71, p.82

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_dsihProblem
import Definitions.Def_SingleInteraction_UniformFamily

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 71 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §6.3, p.82): "There exists a uniform family of 5-local Hermitian matrices
`{ĥ(n)}n≥1` such that `DSIH5` is QMA-complete."

There is a family `{ĥ^(n)}_{n≥1}` of 5-qubit Hermitian matrices, uniform in the sense of
Definition 32, such that `DSIH_5` with this family is in QMA for every exponent `c` and QMA-hard for
some `c`.

**Formalization Note** `UniformFamily` and `dsihProblem` are the published base definitions (`n` the
final number of physical qubits; unweighted copies of `ĥ^(n)` on pairwise distinct ordered 5-tuples of
distinct qubits). QMA notions as in the published `theorem_60`. -/
theorem theorem_71 :
    ∃ hfam : ℕ → Matrix (Fin 5 → Fin 2) (Fin 5 → Fin 2) ℂ,
      (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian) ∧ UniformFamily hfam ∧
        (∀ c : ℕ, InQMA (onCodes sihCodec (dsihProblem 5 hfam c))) ∧
          ∃ c : ℕ, QMAHard sihCodec.encode (dsihProblem 5 hfam c) := by sorry

end Supplement

end SingleInteraction
