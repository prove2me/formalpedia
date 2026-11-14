-- Prove2me | Theorems.Thm_SeymourThomas1993_bramble_of_not_treewidth_le
-- name    : SeymourThomas1993.bramble_of_not_treewidth_le
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T19:58:36.570521+00:00
-- url     : https://prove2.me/theorems/be04ca25-89d0-4537-ae58-7c45ce7323b5
-- title:
--   Treewidth–bramble duality: large treewidth gives a bramble
-- statement:
--   Let G be a finite graph and w a nonnegative integer. If G has no finite tree decomposition with every bag of size at most w+1, then G has a finite bramble of order at least w+2. Its members are nonempty connected vertex sets, any two touch, and no vertex set of size at most w+1 meets all members. This is the large-treewidth direction of the classical treewidth–bramble min-max theorem, before converting a bramble into a haven.
-- source:
--   Seymour and Thomas, Graph searching and a min-max theorem for tree-width, JCTB 58 (1993), pp. 22-33, https://thomas.math.gatech.edu/PAP/search.pdf. Also Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, Theorem 1 and forward proof on p. 3.

import Definitions.Def_SeymourThomas1993_Brambles
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

namespace SeymourThomas1993
theorem bramble_of_not_treewidth_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ family : Finset (Finset V), IsBramble G family ∧ OrderAtLeast family (w+2) := by sorry
end SeymourThomas1993
