-- Prove2me | Theorems.Thm_SethiChengSS_Infinite_vTrunc_kconvex
-- name    : SethiChengSS.Infinite.vTrunc_kconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:31.772118+00:00
-- url     : https://prove2.me/theorems/6710b056-7ab6-47b6-a7cd-74e7bfc80a45
-- title:
--   Proof of Theorem 6.2, p. 937 — the truncated values v_{n,k}(i, ·) are K^i_n-convex
-- statement:
--   Under the standing assumptions (2.1)–(2.2), assumptions (4.1) and (4.2) for every period, and $0 < \alpha < 1$, the value $v_{n,k}(i,\cdot)$ of the $k$-period truncation (6.4) is $K^i_n$-convex for every $n$, $k$ and $i$: for all $z \ge 0$, $b > 0$ and $y$,
--   $$K^i_n + v_{n,k}(i, z+y) \ge v_{n,k}(i,y) + z\,\frac{v_{n,k}(i,y) - v_{n,k}(i,y-b)}{b}.$$
--
--   This is the induction of Section 4 run on the truncated equations (6.5); the $K$-convexity then passes to the limit $k \to \infty$.
--
--   **Formalization Note.** $K$-convexity is the platform definition `BertsekasKConvex` (Definition 4.1 of the paper, (4.3)). Theorem 6.2 as printed omits (4.1), but its proof uses "the same induction as in Section 4", which needs (4.1); it is assumed here for every period.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 937, proof of Theorem 6.2, second sentence

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Infinite_Model

namespace SethiChengSS.Infinite

theorem vTrunc_kconvex {L : ℕ} (D : Model L) (α : ℝ) (hD : Standing D) (h41 : Cond41 D)
    (h42 : Cond42 D) (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ n k i, BertsekasKConvex (D.K n i) (fun x => (vTrunc D α n k i x).toReal) := by sorry

end SethiChengSS.Infinite
