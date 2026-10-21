-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_tableauBranching
-- name    : QAlgorithms.Papers.Independent.Next46.P26.tableauBranching
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:07:01.542191+00:00
-- url     : https://prove2.me/theorems/d68d1968-ad44-48a7-8907-e78fc6126034
-- title:
--   Tableau branching by removing the largest label
-- statement:
--   Let $\lambda$ be a nonempty finite Young diagram and let $\operatorname{SYT}(\lambda)$ denote its standard Young tableaux. Sum over exactly the Young diagrams $\mu$ with $[\mu]\subseteq[\lambda]$ and $|\mu|+1=|\lambda|$. Then
--   $$
--   |\operatorname{SYT}(\lambda)|=\sum_{\mu\to\lambda}|\operatorname{SYT}(\mu)|.
--   $$
--   This is the branching identity induced by deleting the largest label. For a singleton shape, its only predecessor is empty and has one tableau.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 3, BR, §1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- BR, tableau branching by deleting the largest label (§1, pp.1,3).
The oneBoxPredecessors are exactly the one-box smaller Young diagrams. -/
theorem tableauBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    tableauCount lam = ∑ mu ∈ oneBoxPredecessors lam, tableauCount mu := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
