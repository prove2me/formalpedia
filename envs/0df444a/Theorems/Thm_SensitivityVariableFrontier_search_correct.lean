-- Prove2me | Theorems.Thm_SensitivityVariableFrontier_search_correct
-- name    : SensitivityVariableFrontier.search_correct
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-29T00:20:00.36398+00:00
-- url     : https://prove2.me/theorems/8ee54f77-084c-412f-b44c-194271647bad
-- title:
--   Variable-parameter dominance-pruned search is sound and complete at every depth
-- statement:
--   For any valid graph and labeling datum $G$, natural state count $N$, and natural depth $k$,
--
--   $$
--   \operatorname{succeeds}(G,N,k)=\mathrm{true}
--   \quad\Longleftrightarrow\quad
--   \exists w:\ |w|=k,\ \operatorname{Crosses215}_G(w).
--   $$
--
--   On the left, the finite search enumerates bounded recipe letters and removes componentwise dominated profiles only within the same depth. On the right, the word consists of arbitrary recipes subject to the original validity and tolerance conditions. Its output starts from the all-ones upper-triangular profile and uses the original interval-envelope transfer. The crossing predicate includes nonemptiness and the exact integer inequality $H^{43}<K^{20|w|}$.
--
--   The theorem covers every finite depth, with no fixed graph size or tolerance count. It establishes correctness of the search, not that the search succeeds. The mission uses the positive-state instances $N=n+1$.
-- source:
--   Original exact checked-search reduction of SensitivityVariableWord.exists_215_word, https://prove2.me/theorems/b44a1e84-fdd6-4a5c-a770-91fc1133a055. Source definitions: SensitivityVariableWord.GraphData, step, run, Admissible, Crosses215, https://prove2.me/definitions/1a0f2c01-d616-4449-b679-77a45b8e1182. The variable alphabet and pruning proof generalize the fixed-parameter theorem SensitivityWordFrontier.search_correct, https://prove2.me/theorems/39c67854-b4b0-4292-b640-97e0bef4941e. RawData.Valid reproduces every GraphData field as a finite predicate with Boolean adjacency. Underlying recurrence attribution remains yousofy with Codex, OpenAI/math, Robin Kothari with Codex, and earlier community foundations, via accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a at https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2. No source is claimed to supply a crossing input or prove the remaining 2.15 existence claim.

import Definitions.Def_SensitivityVariableFrontier

theorem SensitivityVariableFrontier.search_correct
    (G : SensitivityVariableWord.GraphData) (n k : ℕ) :
    SensitivityVariableFrontier.succeeds G n k = true ↔
    ∃ word : List (SensitivityProfileCycle.Recipe n),
      word.length = k ∧ SensitivityVariableWord.Crosses215 G word := by sorry
