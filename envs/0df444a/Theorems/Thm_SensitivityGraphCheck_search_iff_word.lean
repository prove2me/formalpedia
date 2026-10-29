-- Prove2me | Theorems.Thm_SensitivityGraphCheck_search_iff_word
-- name    : SensitivityGraphCheck.search_iff_word
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-29T00:21:19.57263+00:00
-- url     : https://prove2.me/theorems/e0c956a3-eea9-4351-b70b-34e1f1634dc4
-- title:
--   Checked finite search is equivalent to the variable-parameter word frontier
-- statement:
--   A checked search succeeds at some positive state count and finite depth if and only if the variable-parameter word frontier has a witness:
--
--   $$
--   \bigl(\exists D,n,k:\ \operatorname{checkedSearch}(D,n+1,k)=\mathrm{true}\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(\exists G,n,w:\ \operatorname{Crosses215}_G(w)\bigr).
--   $$
--
--   Here $D$ is raw finite graph and labeling data with no proof fields. Its check includes every tournament, cutoff, coherence, defect, and source condition required of $G$. The word on the right has $n+1$ states. Its graph parameters, tolerance range, length, and recipes may all vary.
--
--   The equivalence removes graph proof obligations and unbounded recipe choices from each fixed candidate verification. Both sides retain an unbounded outer existence problem. No successful input or 2.15 construction is asserted.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityGraphCheck

theorem SensitivityGraphCheck.search_iff_word :
    (∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphCheck.succeeds D (n + 1) k = true) ↔
    ∃ (G : SensitivityVariableWord.GraphData) (n : ℕ)
      (word : List (SensitivityProfileCycle.Recipe (n + 1))),
      SensitivityVariableWord.Crosses215 G word := by sorry
