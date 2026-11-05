-- Prove2me | Theorems.Thm_RotationLadder_Protocol_ladder_reaches
-- name    : RotationLadder.Protocol.ladder_reaches
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:35.948421+00:00
-- url     : https://prove2.me/theorems/a2fbb3d0-a574-44d8-acbc-640c1373fa01
-- title:
--   Every level of the ladder is reached at finite mean cost
-- statement:
--   For every level $i\ge0$, the walk of Fig. 3 reaches level $i$ almost surely, and the expected number of copies of $|H\rangle$ consumed to produce $|H_i\rangle$ is finite.
--
--   This is what makes every rotation of Table I available in the protocol.
--
--   Differences from the source:
--   - reading: each step costs one copy, except the first node, which costs two, and two new copies after outcome 1 there (p. 3, Fig. 3) → a walk from a level −1, no state held, with one copy per transition; reason: gives exactly the paper's counts at every node
--   - reading: the walk of Fig. 3 is described with its cost per step, and no termination claim is written → almost sure arrival at finite expected cost; reason: the protocol's use of |H_i⟩ on p. 4 assumes each ladder ends with the state
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. II, unnumbered, p. 3, Fig. 3

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderMeanCost
open scoped ENNReal

namespace RotationLadder.Protocol

/-- **Every level of the ladder is reached.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. II, unnumbered, p. 3 and Fig. 3.

Almost surely the walk of Fig. 3 reaches level `i`, and the expected number of copies of `|H⟩`
consumed is finite.

**Formalization Note.** The costs are the `ℕ∞`-valued `ladderCost`, coerced to `ℝ≥0∞`, so a positive
chance of never arriving would make the mean `⊤`. -/
theorem ladder_reaches :
    ∀ i : ℕ, (∀ᵐ u ∂ladderLaw, ladderCost i u < ⊤) ∧ ladderMeanCost i < ⊤ := by sorry

end RotationLadder.Protocol
