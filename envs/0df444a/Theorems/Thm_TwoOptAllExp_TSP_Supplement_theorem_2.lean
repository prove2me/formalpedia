-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_theorem_2
-- name    : TwoOptAllExp.TSP.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:45:40.695463+00:00
-- url     : https://prove2.me/theorems/ceb72b90-12ce-4313-aca0-0f806d594b14
-- title:
--   Theorem 2 — $(3,2,2)$-MCA with the flip neighborhood has the all-exp property
-- statement:
--   $(3,2,2)$-Maximum Constraint Assignment (every constraint has at most three variables, every variable appears in at most two constraints, variables are binary, weights are arbitrary integers) with the flip neighborhood has the **all-exp property**: there are $\varepsilon>0$ and $C>0$ such that for every $m$ there are an instance $I$ of encoding size at least $m$ and an initial assignment $s$ from which a maximal improving flip sequence exists and every maximal improving flip sequence has length at least
--
--   $$C\cdot 2^{\,\mathrm{size}(I)^{\varepsilon}}.$$
--
--   Equivalently, the standard local-search algorithm needs exponentially many iterations under every pivot rule on infinitely many instance–start pairs. It is the first of the paper's two MCA results closing the all-exp gap for bounded-occurrence MCA.
--
--   Differences from the source:
--   - encoding: all-exp property of Definition 4 (infinitely many instance/initial-solution pairs, every pivot rule needs Ω(2^{n^ε}) iterations) → published HasAllExpProperty: ∃ ε > 0, C > 0, ∀ m, an instance of size ≥ m and an initial assignment with a maximal improving sequence, every one of length ≥ C·2^{size^ε}; reason: the base mission's Definition 4; every run of a pivot rule is a maximal improving sequence and conversely, and finitely many instances have each size
--   - encoding: instance size → binary encoding size counting variables, constraints, scope indices and every table entry with its sign; reason: any reasonable binary encoding is polynomially related, which the existential ε absorbs
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Theorem 2, p. 8 (also p. 5; proof p. 12)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA

namespace TwoOptAllExp.TSP.Supplement

/-- **Theorem 2** (p. 8; also p. 5): `(3, 2, 2)`-MCA with the flip neighborhood has the all-exp
property (Definition 4, p. 7). -/
theorem theorem_2 : HasAllExpProperty (mcaFlip 3 2) := by sorry

end TwoOptAllExp.TSP.Supplement
