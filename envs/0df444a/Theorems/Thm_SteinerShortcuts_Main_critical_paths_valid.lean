-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_critical_paths_valid
-- name    : SteinerShortcuts.Main.critical_paths_valid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T15:40:42.941502+00:00
-- url     : https://prove2.me/theorems/1180a8f3-11bc-4c50-a051-27ab1c92341d
-- title:
--   Critical paths stay inside the optimized construction
-- statement:
--   Let $L,q$ be admissible construction parameters: $L\ge4$ is even and $q$ is prime with $L\le q\le2L$. Every critical route determined by a source in the prescribed source box and two direction labels is a valid path in the optimized construction, and every vertex of that route belongs to its finite vertex set:
--
--   $$
--   P\in\mathcal P\quad\Longrightarrow\quad P\text{ is a path in }G\text{ and }V(P)\subseteq V.
--   $$
--
--   This is the containment assertion preceding equation (11). It supplies the path-validity prerequisite for the test-function argument independently of the cardinality estimates.
-- source:
--   Bernstein, Fleischmann, Haeupler, Hoppenworth and Saranurak, Polynomial Lower Bounds for Steiner Shortcuts via Test Functions, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf, printed p.22 (PDF p.24), Section 3.2, paragraph immediately before equation (11); coordinate update (2) and the displayed source and vertex boxes.

import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

theorem critical_paths_valid (L q : ℕ) (h : Admissible L q) :
    ∀ P ∈ criticalPaths L q, IsPath (construction L q) P ∧
      ∀ v ∈ P.vertices, v ∈ vertices L q := by sorry

end SteinerShortcuts.Main
