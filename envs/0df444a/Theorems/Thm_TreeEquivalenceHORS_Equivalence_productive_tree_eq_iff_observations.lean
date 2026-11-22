-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_productive_tree_eq_iff_observations
-- name    : TreeEquivalenceHORS.Equivalence.productive_tree_eq_iff_observations
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T18:16:00.506234+00:00
-- url     : https://prove2.me/theorems/e1c0d31d-a67f-424d-962b-fbe418516d9c
-- title:
--   Equality of productive value trees is determined by their positive observations
-- statement:
--   Two well-formed productive schemes over the same ranked alphabet generate equal value trees exactly when any two terminals observed at the same address have the same label.
-- source:
--   Mingkun Xiao and Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, §§3 and 5.6. https://arxiv.org/html/2610.39678v1

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics

namespace TreeEquivalenceHORS.Equivalence

theorem productive_tree_eq_iff_observations {G H : HORS} (hG : G.Valid) (hH : H.Valid)
    (alpha : G.alphabet = H.alphabet) (pg : G.Prod) (ph : H.Prod) :
    G.BT = H.BT ↔ ∀ w a b, a < G.alphabet.length → b < H.alphabet.length →
      G.Obs (.nt G.start) w a → H.Obs (.nt H.start) w b → a = b := by sorry

end TreeEquivalenceHORS.Equivalence
