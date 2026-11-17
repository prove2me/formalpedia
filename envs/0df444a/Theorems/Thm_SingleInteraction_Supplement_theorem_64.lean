-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_64
-- name    : SingleInteraction.Supplement.theorem_64
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:10:04.21454+00:00
-- url     : https://prove2.me/theorems/9f2ddf36-8d2a-47c4-bf2d-3ef162a39042
-- title:
--   Theorem 64 — SIH$_3$ with $g_H=h_H\otimes\Pi_{|1\rangle}+2I\otimes\Pi_{|0\rangle}$ is QMA-complete
-- statement:
--   Let $h_H=X\otimes X+Y\otimes Y+Z\otimes Z$ and
--   $$g_H=h_H\otimes\Pi_{|1\rangle}+2I\otimes\Pi_{|0\rangle},$$
--   with the third qubit as the selector. Then $g_H$ is Hermitian with polynomial-time computable entries, and SIH$_3$ with the fixed interaction $g_H$ is QMA-complete. In particular there is a fixed 3-local Hermitian interaction whose SIH$_3$ problem is QMA-complete.
--
--   This gives a nonperturbative route to QMA-completeness of an unweighted single-interaction problem, at locality three.
--
--   Differences from the source:
--   - encoding: X-complete, with poly(n) bit lengths and an inverse-polynomial gap → membership for every exponent c and X-hardness for some c of the problem at exponent c; reason: the published theorem_60 convention; hardness at c implies hardness at every c′ ≥ c because the valid sets grow
--   - reading: QMA (Definition 2, p.16; an adapted, equivalent form by Remark 1) → the published InQMA / QMAHard: uniform polynomial-size {H, T, CNOT} verifiers, completeness 2/3, soundness 1/3, polynomial-time many-one reductions; reason: the base mission’s declared reading of Definition 2 (Remark 1 calls it equivalent to the standard class)
--   - reading: There exists a fixed 3-local Hermitian interaction g_H … In particular, one may take g_H = … → the statement for the named g_H; reason: it implies the existential first sentence
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 64, p.70

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihProblem
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Interactions

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 64 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §5.3, p.70): "There exists a fixed 3-local Hermitian interaction `gH` such
that the corresponding `SIH3` problem is QMA-complete. In particular, one may take
`gH = hH ⊗ Π|1⟩ + 2I ⊗ Π|0⟩`."

For `g_H = h_H ⊗ Π|1⟩ + 2I ⊗ Π|0⟩` with `h_H = X⊗X + Y⊗Y + Z⊗Z` (the third qubit is the selector):
`g_H` is Hermitian with polynomial-time computable entries, and `SIH_3` with interaction `g_H` is in
QMA for every exponent `c` and QMA-hard for some `c`.

**Formalization Note** As in the published `theorem_60`: `InQMA` / `QMAHard` through `sihCodec`,
membership for every `c`, hardness for some `c`. Naming `g_H` states the "In particular", which implies
the existential first sentence. -/
theorem theorem_64 :
    gH.IsHermitian ∧ EntriesPolyTime gH ∧
      (∀ c : ℕ, InQMA (onCodes sihCodec (sihProblem 3 gH c))) ∧
        ∃ c : ℕ, QMAHard sihCodec.encode (sihProblem 3 gH c) := by sorry

end Supplement

end SingleInteraction
