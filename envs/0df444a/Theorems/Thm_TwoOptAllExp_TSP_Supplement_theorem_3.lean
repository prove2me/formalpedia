-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_theorem_3
-- name    : TwoOptAllExp.TSP.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:53:14.696015+00:00
-- url     : https://prove2.me/theorems/29800ab0-3a27-4f54-b8d8-e520fb7c54a6
-- title:
--   Theorem 3 — $(2,3,2)$-MCA with the flip neighborhood has the all-exp property
-- statement:
--   $(2,3,2)$-Maximum Constraint Assignment (every constraint has at most two variables, every variable appears in at most three constraints, variables are binary, weights are arbitrary integers) with the flip neighborhood has the **all-exp property**: there are $\varepsilon>0$ and $C>0$ such that for every $m$ there are an instance $I$ of encoding size at least $m$ and an initial assignment $s$ from which a maximal improving flip sequence exists and every maximal improving flip sequence has length at least
--
--   $$C\cdot 2^{\,\mathrm{size}(I)^{\varepsilon}}.$$
--
--   Together with Theorem 2 this settles the all-exp property for the bounded-occurrence binary MCA classes left open before.
--
--   Differences from the source:
--   - encoding: all-exp property of Definition 4 (infinitely many instance/initial-solution pairs, every pivot rule needs Ω(2^{n^ε}) iterations) → published HasAllExpProperty: ∃ ε > 0, C > 0, ∀ m, an instance of size ≥ m and an initial assignment with a maximal improving sequence, every one of length ≥ C·2^{size^ε}; reason: the base mission's Definition 4; every run of a pivot rule is a maximal improving sequence and conversely, and finitely many instances have each size
--   - encoding: instance size → binary encoding size counting variables, constraints, scope indices and every table entry with its sign; reason: any reasonable binary encoding is polynomially related, which the existential ε absorbs
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Theorem 3, p. 35 (also pp. 5, 24; proof p. 35)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA

namespace TwoOptAllExp.TSP.Supplement

/-- **Theorem 3** (p. 35; also pp. 5, 24): `(2, 3, 2)`-MCA with the flip neighborhood has the
all-exp property (Definition 4, p. 7). -/
theorem theorem_3 : HasAllExpProperty (mcaFlip 2 3) := by sorry

end TwoOptAllExp.TSP.Supplement
