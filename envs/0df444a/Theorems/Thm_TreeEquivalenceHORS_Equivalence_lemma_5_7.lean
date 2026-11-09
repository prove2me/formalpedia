-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_7
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:17.117739+00:00
-- url     : https://prove2.me/theorems/1cf43e5f-4ae4-49e3-b72a-cf5526a5c2f1
-- title:
--   Lemma 5.7 (Productivity): both compiled schemes are productive
-- statement:
--   For every two-counter program $M$ and side $\diamond\in\{L,R\}$, the compiled scheme $G^\diamond_M$ is productive: its start term is productive to every depth. This includes the arithmetic observation subtrees, illegal candidate branches and branches whose signed weight is zero.
--
--   Differences from the source: none.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.7, printed p. 20 / PDF p. 22

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.7 (Productivity)** (printed p. 20 / PDF p. 22). Both compiled schemes are productive. -/
theorem lemma_5_7 (M : Machine) (side : Side) : (compile side M).Prod := by sorry

end TreeEquivalenceHORS.Equivalence
