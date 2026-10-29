-- Prove2me | Theorems.Thm_SensitivityGraphCheck_exists_215_success
-- name    : SensitivityGraphCheck.exists_215_success
-- status  : Open
-- author  : @dmilosch
-- created : 2026-10-29T00:21:17.668214+00:00
-- url     : https://prove2.me/theorems/6d9893d7-40bb-47ea-acc7-3d8575b5e246
-- title:
--   A finite checked graph-and-profile search reaches the 2.15 threshold
-- statement:
--   Find raw finite graph and labeling data $D$, a positive state count $n+1$, and a natural depth $k$ such that
--
--   $$\operatorname{checkedSearch}(D,n+1,k)=\mathrm{true}.$$
--
--   The checker verifies every original graph, labeling, and cutoff requirement and then runs the exact finite profile search with safe dominance pruning. Success means a retained profile of height $H$ satisfies $H^{43}<K^{20k}$, where $K$ is the vertex count in $D$.
--
--   There are no graph proof fields or freely chosen recipe sequences in the input. All numerical parameters and graph and labeling tables may vary. The correctness theorem makes this an equivalent residual problem for the variable-parameter word frontier. This is an open existence statement: no successful input, bound on its size or depth, or 2.15 separation is supplied or claimed to be known.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityGraphCheck

theorem SensitivityGraphCheck.exists_215_success :
    ∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphCheck.succeeds D (n + 1) k = true := by sorry
