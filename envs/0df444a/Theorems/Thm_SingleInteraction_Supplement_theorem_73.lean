-- Prove2me | Theorems.Thm_SingleInteraction_Supplement_theorem_73
-- name    : SingleInteraction.Supplement.theorem_73
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:12:50.708339+00:00
-- url     : https://prove2.me/theorems/ba223bc5-9429-4cc8-87c6-949ff2a9830f
-- title:
--   Theorem 73 — Stoq-SIH$_3$ with $g_S=h_S\otimes\Pi_{|1\rangle}+5I\otimes\Pi_{|0\rangle}$ is StoqMA-complete
-- statement:
--   Let $h_S=-X\otimes X+Y\otimes Y+2Z\otimes Z$ and
--   $$g_S=h_S\otimes\Pi_{|1\rangle}+5I\otimes\Pi_{|0\rangle}.$$
--   Then $g_S$ is Hermitian, stoquastic in the computational basis, and has polynomial-time computable entries, and the Stoq-SIH$_3$ problem with the fixed interaction $g_S$ is StoqMA-complete. In particular there is a fixed 3-local stoquastic Hermitian interaction whose Stoq-SIH$_3$ problem is StoqMA-complete.
--
--   This is the stoquastic counterpart of Theorem 64.
--
--   Differences from the source:
--   - encoding: StoqMA-complete → membership in StoqMA for every exponent c and StoqMA-hardness for some c; reason: the published theorem_60 convention
--   - reading: StoqMA thresholds ϵyes, ϵno with inverse-polynomial gap (Definition 5) → thresholds computable to precision 2^{−q} in polynomial time, gap ≥ 1/(|x|+1)^d; reason: Definition 5 leaves their computability implicit; the class of [BBT06] and every reduction of the paper compute them
--   - reading: There exists a fixed 3-local stoquastic Hermitian interaction g_S … In particular, one may take g_S = … → the statement for the named g_S; reason: it implies the existential first sentence
--   - reading: a finite gate set universal for classical reversible computation, output qubit measured in the Hadamard basis (Definition 5) → the gates X, CNOT, Toffoli, output qubit 0 measured in the Hadamard basis, accepting on +; reason: the gate set of [BBT06]; any two finite classical-reversible universal gate sets simulate each other with polynomial overhead given the |0⟩, |1⟩ ancillas of Definition 5
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Theorem 73, p.85

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihProblem
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_Supplement_Linalg
import Definitions.Def_SingleInteraction_Supplement_StoqMA
import Definitions.Def_SingleInteraction_Supplement_Interactions

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-- Theorem 73 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held
version, sha256 19ddc444…), §7.1, p.85): "There exists a fixed 3-local stoquastic Hermitian interaction
`gS` such that the corresponding Stoq-`SIH3` problem is StoqMA-complete. In particular, one may take
`gS = hS ⊗ Π|1⟩ + 5I ⊗ Π|0⟩`."

For `g_S = h_S ⊗ Π|1⟩ + 5I ⊗ Π|0⟩` with `h_S = −X⊗X + Y⊗Y + 2Z⊗Z`: `g_S` is Hermitian, stoquastic in
the computational basis, with polynomial-time computable entries, and Stoq-`SIH_3` with interaction
`g_S` is in StoqMA for every exponent `c` and StoqMA-hard for some `c`.

**Formalization Note** Stoq-`SIH_3` with `g_S` is `sihProblem 3 gS` (Definition 33 restricts only the
interaction, asserted by `IsStoquastic gS`). StoqMA follows Definition 5 (`InStoqMA`, gate set
`{X, CNOT, Toffoli}`, Hadamard-basis output measurement, efficiently computable thresholds with an
inverse-polynomial gap, no amplification). Membership for every `c`, hardness for some `c`. -/
theorem theorem_73 :
    gS.IsHermitian ∧ IsStoquastic gS ∧ EntriesPolyTime gS ∧
      (∀ c : ℕ, InStoqMA (onCodes sihCodec (sihProblem 3 gS c))) ∧
        ∃ c : ℕ, StoqMAHard sihCodec.encode (sihProblem 3 gS c) := by sorry

end Supplement

end SingleInteraction
