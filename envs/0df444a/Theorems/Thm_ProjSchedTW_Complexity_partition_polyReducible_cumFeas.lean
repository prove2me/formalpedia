-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_partition_polyReducible_cumFeas
-- name    : ProjSchedTW.Complexity.partition_polyReducible_cumFeas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:09:29.869775+00:00
-- url     : https://prove2.me/theorems/81aa0cce-42ec-44b4-9d90-4c2bd2ef2130
-- title:
--   Proof of Theorem 2.12.1 — PARTITION reduces in polynomial time to feasibility for acyclic PSc|temp|C_max
-- statement:
--   Let PARTITION be the binary-coded language of yes-instances of PARTITION, and $L_{\mathrm{acyc}}$ the language of codes of well-formed instances of $PSc|temp|C_{\max}$ with an acyclic project network that have a feasible schedule. Then
--   $$\mathrm{PARTITION}\ \le_p\ L_{\mathrm{acyc}},$$
--   that is, some function computable in polynomial time by a Turing machine maps every string $x$ to a string $f(x)$ with $x\in\mathrm{PARTITION}\iff f(x)\in L_{\mathrm{acyc}}$.
--
--   This is the book's "polynomial transformation from PARTITION" in the proof of Theorem 2.12.1, stated as a many-one reduction between the two languages.
--
--   **Formalization Note** $\le_p$ is `CookPvsNP.PolyReducible` (Cook's Definition 3). Strings that are not codes of PARTITION instances, PARTITION instances with an odd total size, and the instance with $\nu=0$ (the book's projects have $n\ge1$) must also be mapped correctly; the book's construction covers the well-formed even case.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 130–131, proof of Theorem 2.12.1, second paragraph (polynomial transformation from PARTITION)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative

namespace ProjSchedTW.Complexity

/-- Proof of Theorem 2.12.1 (pp. 130–131): PARTITION reduces in polynomial time to the
feasibility problem of `PSc|temp|C_max` restricted to acyclic project networks. -/
theorem partition_polyReducible_cumFeas :
    CookPvsNP.PolyReducible partitionLang (cumFeasLang CumInstance.IsAcyclic) := by sorry

end ProjSchedTW.Complexity
