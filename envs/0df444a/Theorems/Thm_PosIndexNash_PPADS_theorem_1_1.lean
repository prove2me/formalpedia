-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_theorem_1_1
-- name    : PosIndexNash.PPADS.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:34:43.375231+00:00
-- url     : https://prove2.me/theorems/10f2c88f-3391-4c00-acd5-05a8b62c8ca8
-- title:
--   Theorem 1.1 — Positive-Index Nash is PPADS-complete
-- statement:
--   **Main theorem.** The promise search problem Positive-Index Nash — given a nondegenerate rational bimatrix game $(A, B)$, find an exact Nash equilibrium $(x, y)$ with Shapley index $\mathrm{ind}_{A,B}(x, y) = +1$ — is **PPADS-complete**:
--   $$\textsc{Positive-Index Nash} \in \mathrm{PPADS}\qquad\text{and}\qquad R \le_p \textsc{Positive-Index Nash}\ \text{ for every } R \in \mathrm{PPADS},$$
--   where PPADS is the class of search problems that reduce in polynomial time to normalized Sink-of-Line. Its membership reduction is required to be correct only on promised (nondegenerate) inputs, and its hardness reductions always output promised, globally nondegenerate games.
--
--   Allowing an arbitrary Nash equilibrium gives a PPAD-complete problem; requiring index $+1$ captures the sink-only class PPADS.
--
--   Differences from the source:
--   - encoding: games, equilibria and circuits; "polynomial-time reduction" → binary codes (`RatGame.enc`, `encRatVec`, `encCircuit`) and `CardinalMatching.SearchReduces` on Cook Turing machines, which checks correctness on valid instances only and requires the instance map to output valid instances; reason: standard encoding; the two extra clauses of the theorem (membership on promised inputs only, hardness outputs promised games) are exactly this promise semantics, with nondegeneracy in `valid` (p. 14).
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 5, Theorem 1.1 (proof p. 51)

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_PPADSClass
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash

namespace PosIndexNash.PPADS

theorem theorem_1_1 : PPADSComplete PositiveIndexNash := by sorry

end PosIndexNash.PPADS
