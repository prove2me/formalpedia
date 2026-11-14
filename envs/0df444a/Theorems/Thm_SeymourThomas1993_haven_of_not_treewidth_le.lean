-- Prove2me | Theorems.Thm_SeymourThomas1993_haven_of_not_treewidth_le
-- name    : SeymourThomas1993.haven_of_not_treewidth_le
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T18:27:54.556863+00:00
-- url     : https://prove2.me/theorems/7966a3f4-c290-4d22-bc9d-23471cb44e20
-- title:
--   Treewidth–haven duality: large treewidth gives a haven
-- statement:
--   Let $G$ be a finite graph and $w\ge0$ an integer. If $G$ has no tree decomposition of width at most $w$, then $G$ has a haven of order $w+2$. Thus for every vertex set $W$ with $|W|<w+2$ one can choose a nonempty component $\beta(W)$ of $G-W$, such that every two chosen components touch. Tree decompositions have a finite nonempty tree, cover vertices and edges, satisfy the running-intersection property, and have bags of size at most $w+1$. This is the large-treewidth direction of the treewidth/bramble min-max theorem, followed by the standard passage from a bramble to its haven.
-- source:
--   Seymour and Thomas, Graph searching and a min-max theorem for tree-width, J. Combin. Theory Ser. B 58 (1993), pp. 22-33. As stated and converted from brambles to havens in Dvorak--Norin, https://arxiv.org/pdf/1408.3869v2, Theorem 2 and the following two paragraphs, PDF p. 3.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

namespace SeymourThomas1993
theorem haven_of_not_treewidth_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ β : Finset V → Finset V, Haven G (w+2) β := by sorry
end SeymourThomas1993
