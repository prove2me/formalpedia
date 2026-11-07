-- Prove2me | Theorems.Thm_ShortBroadcastDom_sec_1_1_planar_in_C3
-- name    : ShortBroadcastDom.sec_1_1_planar_in_C3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:37.908482+00:00
-- url     : https://prove2.me/theorems/ac6444e8-f1a1-40ed-be40-9eea4bb1ac99
-- title:
--   §1.1 — planar graphs lie in $\mathcal C_3$
-- statement:
--   Every finite planar graph $G$ lies in $\mathcal C_3$: every minor $J$ of $G$ satisfies $|E(J)|\le3|V(J)|$.
--
--   This places planar graphs in clause (i) of Theorem C with $a=3$, giving the coefficient $7$.
--
--   Differences from the source: none.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §1.1, p.2 (PDF p.5)

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom

/-- **Planar graphs lie in `C₃`.** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §1.1, p.2 (PDF 5): "For rational a ≥ 1, let Ca be the class
of graphs whose nonempty minors J satisfy |E(J)| ≤ a|V(J)|. … Every class excluding a fixed minor
lies in some Ca by a classical result of Mader [Mad67], and planar graphs lie in C3."

**Formalization Note** Planarity is the published `RobertsonSeymour1986.GM5.IsPlanar`; graphs are
finite. -/
theorem sec_1_1_planar_in_C3 {V : Type} [Fintype V] (G : SimpleGraph V) (hG : RobertsonSeymour1986.GM5.IsPlanar G) :
    InClassC 3 G := by sorry

end ShortBroadcastDom
