-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_3_2
-- name    : SubquadCutReach.Faster.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:57:32.887084+00:00
-- url     : https://prove2.me/theorems/c8f5a708-bbba-46f4-9eac-b39cce8bd8d2
-- title:
--   Lemma 3.2 — Preserving imbalances preserves reachability
-- statement:
--   Let $G$ be an oriented graph, $H$ its skeleton, and let $D$ be the orientation induced by any all-pair rule on $H$. If $b_D=b_G$, then
--
--   $$F_D(S)=F_G(S)\quad(\forall S\subseteq V),\qquad s\leadsto_D t\ \Longleftrightarrow\ s\leadsto_G t\quad(\forall s,t\in V).$$
--
--   Both conclusions are retained. Reflexive reachability includes $s=t$, and no connectedness assumption is imposed. This identifies exactly which information about directions the protocol needs to recover.
--
--   Differences from the source:
--   - encoding: labelled graphs and orientation rules → Fin n, Mathlib simple graphs and increasing-pair Boolean tables; reason: all finite labelled source graphs and all directions are represented; unused table cells carry no mathematical information
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 6, Lemma 3.2 (PDF p. 8)

import Definitions.Def_SubquadCutReach_Faster_Graphs

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_3_2 {n : ℕ} (G : Digraph n) (hG : Oriented G) (D : Rule n)
    (hb : imbalance (induced (skeleton G hG) D) = imbalance G) :
    (∀ S, outCut (induced (skeleton G hG) D) S = outCut G S) ∧
    ∀ s t, reachable (induced (skeleton G hG) D) s t ↔ reachable G s t := by sorry

end SubquadCutReach.Faster
