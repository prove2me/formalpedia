-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_yplus_exists
-- name    : SongZipkinFluct.Monotone.yplus_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T12:54:53.025877+00:00
-- url     : https://prove2.me/theorems/08d533a1-5d12-412b-982d-a81238fc8b18
-- title:
--   Existence of the myopic basestock levels $y^+(i)$ (smallest minimizers of $G^+(i,\cdot)$)
-- statement:
--   Assume the standing hypotheses of the model and Assumption 1 ($\alpha\bar c < p$). For every world state $i$, the myopic cost
--   $$G^+(i,y) = (1-\gamma)\,c\,y + \beta\, C(i,y),\qquad y\in\mathbb Z,$$
--   has a smallest global minimizer $y^+(i)$ over the integers. Here $C(i,y)=\mathbb E[e^{-\alpha L}\hat C(y-D^i_L)]$ is the discounted expected inventory cost at the end of the lead time.
--
--   The paper (p. 356) defines $y^+(i)$ as the smallest value of $y$ minimizing $G^+(i,y)$; its existence follows from convexity of $G^+(i,\cdot)$ (Lemma 1) and coercivity under Assumption 1 (Lemma 2), p. 355. This is the existence part used in Theorem 8.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 355 (Lemmas 1–2) and p. 356 (definition of the myopic level y⁺(i))

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Model

namespace SongZipkinFluct.Monotone

theorem yplus_exists {I : Type} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) :
    ∃ yplus : I → ℤ, ∀ i, IsSmallestMinimizer (M.Gplus i) (yplus i) := by sorry

end SongZipkinFluct.Monotone
