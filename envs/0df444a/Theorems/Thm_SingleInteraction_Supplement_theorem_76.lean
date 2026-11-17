-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_76
-- name    : SingleInteraction.Supplement.theorem_76
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:14:23.239838+00:00
-- url     : https://prove2.me/theorems/94917e4f-d206-44b9-8ed5-d9cdb2b226aa
-- title:
--   Theorem 76 — a fixed 4-local stoquastic interaction for which 1-Pinned Stoq-SIH$_4$ is QMA-complete
-- statement:
--   There is a fixed 4-qubit Hermitian interaction $h$, stoquastic in the computational basis and with polynomial-time computable entries, such that the 1-Pinned Stoq-SIH$_4$ problem with interaction $h$ is QMA-complete.
--
--   A single pinned qubit thus lifts a stoquastic single-interaction problem from StoqMA to QMA.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
--   - encoding: pinned circuit over a fixed finite gate set, polynomial size → a gate list over {H, T, CNOT} with at most (n+1)^c gates; reason: the base gate set and the instance exponent
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 76, p.87

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_Pinned

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 76 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §7.3, p.87): "There exists a fixed 4-local stoquastic Hermitian interaction
such that the 1-Pinned Stoq-SIH4 problem is QMA-complete."

There is a 4-qubit Hermitian interaction `h`, stoquastic in the computational basis (real entries,
non-positive off-diagonal entries) and with polynomial-time computable entries, such that 1-Pinned
Stoq-`SIH_4` with interaction `h` (Definition 37: one pinned qubit, the energy minimized over the
remaining qubits) is in QMA for every exponent `c` and QMA-hard for some `c`.

**Formalization Note** The pinned problem is `pinnedSihProblem 4 1 h` (pinned circuit over
`{H, T, CNOT}` with at most `(n+1)^c` gates, promise on `λmin` of the compression); Definition 37 is
the restriction to stoquastic `h`, asserted by `IsStoquastic h`. QMA notions as in the published
`theorem_60`, through the pinned-instance codec: membership for every `c`, hardness for some `c`. -/
theorem theorem_76 :
    ∃ h : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ,
      h.IsHermitian ∧ IsStoquastic h ∧ EntriesPolyTime h ∧
        (∀ c : ℕ, InQMA (onCodes pinnedCodec (pinnedSihProblem 4 1 h c))) ∧
          ∃ c : ℕ, QMAHard pinnedCodec.encode (pinnedSihProblem 4 1 h c) := by sorry

end Supplement

end SingleInteraction
