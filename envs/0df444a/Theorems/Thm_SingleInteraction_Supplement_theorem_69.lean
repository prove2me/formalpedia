-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_69
-- name    : SingleInteraction.Supplement.theorem_69
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:11:31.844977+00:00
-- url     : https://prove2.me/theorems/5d8ceecd-6bf4-4f2a-8133-72e5b67a297e
-- title:
--   Theorem 69 — a uniform family $\{h^{(n)}\}$ of 3-local interactions for which 2-Pinned DSIH$_3$ is QMA-complete
-- statement:
--   There is a family $\{h^{(n)}\}_{n\ge1}$ of 3-qubit Hermitian matrices, uniform in the sense of Definition 32 (entries computable from $1^n$ and the precision in polynomial time, $\|h^{(n)}\|\le\mathrm{poly}(n)$), such that the 2-Pinned DSIH$_3$ problem with this family is QMA-complete. Here $n$ is the final number of physical qubits, pinned ones included.
--
--   The interaction depends only on the global system size, never on other instance data.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
--   - encoding: pinned circuit over a fixed finite gate set, polynomial size → a gate list over {H, T, CNOT} with at most (n+1)^c gates; reason: the base gate set and the instance exponent
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 69, p.79

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_UniformFamily
import Definitions.Def_SingleInteraction_Supplement_Pinned

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 69 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §6.2, p.79): "There exists a uniform family of 3-local Hermitian matrices
`{h(n)}n≥1` for which the 2-Pinned `DSIH3` problem is QMA-complete."

There is a family `{h^(n)}_{n≥1}` of 3-qubit Hermitian matrices, uniform in the sense of
Definition 32 (entries computable in time polynomial in `n` and the precision, `‖h^(n)‖ ≤ poly(n)`),
such that 2-Pinned `DSIH_3` (Definition 36) with this family is in QMA for every exponent `c` and
QMA-hard for some `c`.

**Formalization Note** Uniformity is the published `UniformFamily`; the pinned problem is
`pinnedDsihProblem 3 2` (pinned register of two qubits, pinned circuit over `{H, T, CNOT}` with at most
`(n+1)^c` gates, promise on `λmin` of the compression), with `n` the final number of physical qubits.
QMA notions as in the published `theorem_60`, through the pinned-instance codec. -/
theorem theorem_69 :
    ∃ hfam : ℕ → Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ,
      (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian) ∧ UniformFamily hfam ∧
        (∀ c : ℕ, InQMA (onCodes pinnedCodec (pinnedDsihProblem 3 2 hfam c))) ∧
          ∃ c : ℕ, QMAHard pinnedCodec.encode (pinnedDsihProblem 3 2 hfam c) := by sorry

end Supplement

end SingleInteraction
