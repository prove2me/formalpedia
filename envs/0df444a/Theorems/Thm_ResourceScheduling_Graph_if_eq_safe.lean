-- Prove2me | Theorems.Thm_ResourceScheduling_Graph_if_eq_safe
-- name    : ResourceScheduling.Graph.if_eq_safe
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T15:59:26.052482+00:00
-- url     : https://prove2.me/theorems/ef8ffc3f-5352-471f-82d8-5f092e5e9d99
-- title:
--   if eq safe
-- statement:
--   The two-subtraction equality conditional preserves numeric boundedness under the stated scratch-stable branch invariant.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_ReductionProgram
import Definitions.Def_ResourceScheduling_Graph_RAMSafe
open ResourceScheduling.Graph GraphReg GraphProgram

namespace ResourceScheduling.Graph
theorem if_eq_safe (a b : GraphReg) (p q : Code) (B : ℕ) (P : RAMState GraphReg → Prop)
    (hd : ∀ s x, P s → P (s.set delta x)) (ha : ∀ s x, P s → P (s.set aux x))
    (hp : ∀ s, RAMBound B s → P s → RAMSafe p B s)
    (hq : ∀ s, RAMBound B s → P s → RAMSafe q B s)
    (s : RAMState GraphReg) (hs : RAMBound B s) (hP : P s) : RAMSafe (ifEq a b p q) B s := by sorry
end ResourceScheduling.Graph
