-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_5_2
-- name    : TreeEquivalenceHORS.Equivalence.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:52.157653+00:00
-- url     : https://prove2.me/theorems/dab00a45-2055-47c7-b83f-d9edd1e81ab1
-- title:
--   Lemma 5.2 (Safety of the compiler): every compiled scheme $G^\diamond_M$ is safe
-- statement:
--   For every two-counter program $M$ and side $\diamond\in\{L,R\}$, the compiled scheme $G^\diamond_M$ is safe in the sense of Section 3: all nonterminal and body-subterm types are homogeneous, and every application operand $s$ satisfies $\operatorname{ord}(s)\le\operatorname{ord}(x)$ for every rule parameter $x$ occurring in $s$.
--
--   Safety of the compiler output is what places the lower bound in the safe class.
--
--   Differences from the source: none.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 5.2, printed p. 16 / PDF p. 18

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 5.2 (Safety of the compiler)** (printed p. 16 / PDF p. 18). For every `M` and side `⋄`,
the compiled scheme `G^⋄_M` is safe. -/
theorem lemma_5_2 (M : Machine) (side : Side) : (compile side M).Safe := by sorry

end TreeEquivalenceHORS.Equivalence
