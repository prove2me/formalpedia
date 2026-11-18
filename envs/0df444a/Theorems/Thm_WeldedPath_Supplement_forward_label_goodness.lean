-- Prove2me | Theorems.Thm_WeldedPath_Supplement_forward_label_goodness
-- name    : WeldedPath.Supplement.forward_label_goodness
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-18T01:30:58.071572+00:00
-- url     : https://prove2.me/theorems/49ddc5ba-19f4-40c2-9167-eab7558c528f
-- title:
--   Forward-label compression preserves the canonical good space exactly
-- statement:
--   Let $G$ be a valid welded-tree instance, with $n\ge16$ and $2\le\ell\le n-4$. Let $B$ be any set of structural vertices containing the canonical boundary $V_{\mathrm{bd}}(n,\ell)$, and let $t\ge0$ be an integer. Write $\Pi_t^{\mathrm{good}}(B)$ for the canonical good-space projector, extended by the identity on the query register, and $pC_{\mathrm{lab}}^{\mathrm{for}}$ for the literal forward-label compression operator defined by the compressed oracle. Then
--
--   $$
--   (I-\Pi_{t+1}^{\mathrm{good}}(B))\,pC_{\mathrm{lab}}^{\mathrm{for}}\,\Pi_t^{\mathrm{good}}(B)=0.
--   $$
--
--   Thus forward-label compression maps every coherent good state with at most $t$ records into the canonical good space with at most $t+1$ records, with zero leakage. The query register may be arbitrarily superposed and entangled with the database. This is the forward-label part of Lemma 4.8; unlike approximate inverse-label compression, this exact statement needs no small-query or coefficient-stability budget.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, https://arxiv.org/html/2611.05912v1, Section 4.2, Lemma 4.8 (forward-label compression part).

import Definitions.Def_WeldedPath_Supplement_projGood

set_option autoImplicit false

namespace WeldedPath.Supplement

theorem forward_label_goodness {n l : ℕ} (G : WeldedInstance n)
    (hG : G.IsValid) (hn : 16 ≤ n) (hl : 2 ≤ l) (hln : l ≤ n - 4)
    (B : Finset ℕ) (hB : Vbd n l ⊆ B) (t : ℕ) :
    ((1 : Hil (QReg n × Db l G) →L[ℂ] Hil (QReg n × Db l G)) -
      projGoodB l G B (t+1)).comp ((pCforLab l G).comp (projGoodB l G B t)) = 0 := by
  sorry

end WeldedPath.Supplement
