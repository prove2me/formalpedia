-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_deviation_npHard
-- name    : ProjSchedTW.Complexity.deviation_npHard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:10:51.055268+00:00
-- url     : https://prove2.me/theorems/79e9b184-1837-477c-8264-47c278e785fb
-- title:
--   Proposition 3.4.2 — PS∞|temp,d̄| −ΣΣ w_ij|S_j − S_i| is NP-hard
-- statement:
--   Assume that SIMPLE MAX CUT is NP-complete (Karp, 1972; Garey and Johnson, 1979). Then the decision version of $PS\infty|temp,\bar d|-\sum\sum w_{ij}|S_j-S_i|$ is NP-hard: every language in NP reduces in polynomial time to the language of codes of well-formed instances with a time-feasible schedule $S$ satisfying
--   $$\sum_{i\in V}\sum_{j\in V:\,j>i}w_{ij}\,|S_j-S_i|\ \ge\ M.$$
--
--   Maximizing the weighted start-time deviation spreads activities over time (a resource-levelling objective); the proposition says that even without resource constraints this is hard.
--
--   **Formalization Note** The book's statement concerns the optimization problem; it is formalized as NP-hardness of its decision version ("is there a time-feasible $S$ with $f(S)\le-M$?"), the standard reading. NP-hardness is the second conjunct of `CookPvsNP.NPComplete`, written out. The NP-completeness of SIMPLE MAX CUT is a hypothesis. Weights $w_{ij}$ and $M$ are natural numbers; codes are binary.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 241, Proposition 3.4.2 and its proof; objective defined on p. 200 (§3.1); SIMPLE MAX CUT after Garey & Johnson, Computers and Intractability, 1979

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained

namespace ProjSchedTW.Complexity

/-- Proposition 3.4.2 (p. 241), relative to the NP-completeness of SIMPLE MAX CUT: the decision
version of `PS∞|temp,d̄| −∑∑ w_ij|S_j − S_i|` is NP-hard. -/
theorem deviation_npHard (hMaxCut : CookPvsNP.NPComplete maxCutLang) :
    ∀ (Sym' : Type) [Fintype Sym'] [Nonempty Sym'] (L' : CookPvsNP.Lang Sym'),
      L' ∈ CookPvsNP.NP Sym' → CookPvsNP.PolyReducible L' deviationLang := by sorry

end ProjSchedTW.Complexity
