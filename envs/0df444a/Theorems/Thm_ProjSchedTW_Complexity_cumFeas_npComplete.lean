-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_cumFeas_npComplete
-- name    : ProjSchedTW.Complexity.cumFeas_npComplete
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:09:23.417355+00:00
-- url     : https://prove2.me/theorems/5c6fcf1b-5e83-46ff-ab92-4d165aa6c609
-- title:
--   Theorem 2.12.1 — feasibility for PSc|temp|C_max is NP-complete, even for acyclic project networks
-- statement:
--   Assume that PARTITION is NP-complete (Karp, 1972; Garey and Johnson, 1979). Then the problem of testing whether a given instance of $PSc|temp|C_{\max}$ has a feasible schedule is NP-complete, and it stays NP-complete when the project network $N$ is acyclic:
--   $$L\ \text{is NP-complete}\quad\text{and}\quad L_{\mathrm{acyc}}\ \text{is NP-complete}.$$
--   Here $L$ is the language of codes of well-formed instances of $PSc|temp|C_{\max}$ that have a feasible schedule (time-feasible and satisfying $\underline R_k\le r_k(S,t)\le\overline R_k$ for all cumulative resources $k$ and all $t\ge0$), and $L_{\mathrm{acyc}}$ its restriction to acyclic project networks.
--
--   The book stresses the contrast with renewable resources: feasibility with renewable resources is NP-complete as well (Theorem 2.3.13), but on an acyclic network a feasible schedule always exists when every requirement is within capacity. With cumulative resources the feasibility problem stays NP-complete even when $N$ is acyclic.
--
--   **Formalization Note** NP-completeness is `CookPvsNP.NPComplete` (Cook's Definition 4): membership in NP and polynomial-time reducibility of every NP language. The NP-completeness of PARTITION is a hypothesis: it is Karp's theorem, not a result of the book, and is not yet formalized in this framework. Instances are coded in binary (definition file `Cumulative`); real activities may have duration zero.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 130, Theorem 2.12.1 (proof pp. 130–131); PARTITION after Garey & Johnson, Computers and Intractability, 1979

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative

namespace ProjSchedTW.Complexity

/-- Theorem 2.12.1 (p. 130), relative to the NP-completeness of PARTITION: testing whether an
instance of `PSc|temp|C_max` has a feasible schedule is NP-complete, and so is its restriction
to acyclic project networks. -/
theorem cumFeas_npComplete (hPartition : CookPvsNP.NPComplete partitionLang) :
    CookPvsNP.NPComplete (cumFeasLang (fun _ => True)) ∧
      CookPvsNP.NPComplete (cumFeasLang CumInstance.IsAcyclic) := by sorry

end ProjSchedTW.Complexity
