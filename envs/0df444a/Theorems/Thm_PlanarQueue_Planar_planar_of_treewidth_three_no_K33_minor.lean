-- Prove2me | Theorems.Thm_PlanarQueue_Planar_planar_of_treewidth_three_no_K33_minor
-- name    : PlanarQueue.Planar.planar_of_treewidth_three_no_K33_minor
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:39:46.988743+00:00
-- url     : https://prove2.me/theorems/a34e10b3-fa4a-4bca-a4e3-8b998a16e566
-- title:
--   Treewidth at most 3 and no $K_{3,3}$ minor imply planarity
-- statement:
--   Let $G$ be a finite graph of treewidth at most $3$ with no $K_{3,3}$ minor. Then $G$ is planar:
--
--   $$\operatorname{tw}(G)\le 3,\ K_{3,3}\not\preceq G \implies G \text{ planar}.$$
--
--   Role: gives planarity of the quotient $G/\mathcal P$ in Theorem 15 (which also needs $\operatorname{tw}(G/\mathcal P)\le3$).
--
--   **Formalization Note**: treewidth, minors and planarity are the platform's `RobertsonSeymour1986.GM5` notions.
-- source:
--   K. Wagner, Über eine Eigenschaft der ebenen Komplexe, Math. Ann. 114 (1937) 570-590, https://doi.org/10.1007/BF01594196; R. Diestel, Graph Theory, 5th ed., 2017, Theorem 4.4.6 (planar iff no K5 and no K33 minor), with tw(K5) = 4 (Diestel, Section 12.3)

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace PlanarQueue.Planar

theorem planar_of_treewidth_three_no_K33_minor {W : Type} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    (htw : RobertsonSeymour1986.GM5.TreewidthLE G 3)
    (hK : ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G) :
    IsPlanar G := by sorry

end PlanarQueue.Planar
