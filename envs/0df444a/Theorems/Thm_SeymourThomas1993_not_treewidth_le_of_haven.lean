-- Prove2me | Theorems.Thm_SeymourThomas1993_not_treewidth_le_of_haven
-- name    : SeymourThomas1993.not_treewidth_le_of_haven
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T19:58:14.215236+00:00
-- url     : https://prove2.me/theorems/ce9f361c-f52e-487d-ac3d-168467007909
-- title:
--   A haven of order w+2 obstructs treewidth at most w
-- statement:
--   A haven of order w+2 prevents a graph from having a finite tree decomposition whose bags all have size at most w+1. More generally, any finite tree decomposition has a bag meeting every member of any pairwise-touching family of nonempty connected vertex sets. Applied to the components selected by the haven for the decomposition bags, this contradicts the requirement that a selected component avoid its deletion bag. The obstruction holds even for an infinite ambient vertex type when the stated finite decomposition exists.
-- source:
--   Seymour and Thomas, Graph searching and a min-max theorem for tree-width, JCTB 58 (1993), min-max theorem, easy direction. See also Mazoit, https://arxiv.org/pdf/1309.2266, p. 3, backward implication; this proof uses the equivalent Helly property of subtrees.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

namespace SeymourThomas1993
theorem not_treewidth_le_of_haven {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {w : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G (w+2) β) : ¬ TreewidthLE G w := by sorry
end SeymourThomas1993
