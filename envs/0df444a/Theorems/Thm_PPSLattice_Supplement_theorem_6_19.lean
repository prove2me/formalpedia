-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_6_19
-- name    : PPSLattice.Supplement.theorem_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T08:54:31.464041+00:00
-- url     : https://prove2.me/theorems/ede35dea-6ade-459a-8655-c0e8b4341d88
-- title:
--   Theorem 6.19 — adaptive evolving-graph CSS from robust PPS
-- statement:
--   If an RPPS is correct, compact, and robustly payload hiding for a message family containing both one-bit strings, Construction 6.17 is an adaptively secure evolving-graph CSS with unbounded collusion and degree, polynomial-size vertex shares, and the RPPS public parameters for $2^\lambda$ indices as public share.
--
--   Differences from the source:
--   - generalization: The paper uses the one-bit message space → Lean permits any message family containing both one-bit strings; reason: specializing the family to exactly the two one-bit strings gives the source theorem.
--   - reading: Definition 6.16 quantifies over graph lengths while Construction 6.17 fixes the RPPS index space to $2^\lambda$ → Lean makes the proof's implicit PPT-execution bound explicit as $L\le 2^\lambda$ in correctness; reason: every PPT interaction has polynomially many vertices and hence satisfies this bound asymptotically, while indices beyond $2^\lambda$ are outside the construction's stated RPPS space.
--   - encoding: The source says unbounded collusion and degree as logarithmic dependence on supplied bounds → Lean evaluates both bounds at $2^\lambda$ and gives a support-wise polynomial share bound; reason: the bounds are passed in binary, so this is the source's unbounded regime.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 6.19, p.53

import Mathlib
import Definitions.Def_PPSLattice_Supplement_EvolvingCSS
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 6.19**, Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
p.53. A robust PPS whose message space contains the two bits makes Construction 6.17 an
adaptively secure CSS scheme for evolving graphs, with unbounded collusion and degree,
`poly(λ)` vertex shares, and the RPPS public parameters for `2^λ` indices as public share.

**Formalization Note.** The adversary chooses neighborhoods and corruptions in either order; only
the final corrupted set must be independent. `Q=Δ=2^λ` is passed in binary for the unbounded
variants. -/
theorem theorem_6_19 (E : RPPS) (Message : ℕ → Set QAlgorithms.Complexity.Str)
    (hbits : ∀ lam, ([false] : QAlgorithms.Complexity.Str) ∈ Message lam ∧
      ([true] : QAlgorithms.Complexity.Str) ∈ Message lam)
    (hE : E.IsScheme Message) :
    (construction617 E).IsScheme ∧ (construction617 E).UnboundedCollusionDegree ∧
      Construction617PublicShare E (construction617 E) := by sorry

end PPSLattice.Supplement
