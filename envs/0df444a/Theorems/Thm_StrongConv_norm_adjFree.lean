-- Prove2me | Theorems.Thm_StrongConv_norm_adjFree
-- name    : StrongConv.norm_adjFree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:51:06.394381+00:00
-- url     : https://prove2.me/theorems/12dba20f-4ddc-4229-9c0d-2d0c9a5aa43b
-- title:
--   Kesten's theorem — the 2d-regular tree has norm 2√(2d−1)
-- statement:
--   For every $d \ge 1$, the adjacency operator $A_{\rm F} = s_1 + s_1^* + \cdots + s_d + s_d^*$ of the Cayley graph of $\mathbf F_d$ (the $2d$-regular tree), acting on $l^2(\mathbf F_d)$ by the left-regular representation, has operator norm $\|A_{\rm F}\| = 2\sqrt{2d-1}$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 9, Kesten's theorem, the norm of the 2d-regular tree, which cites Kesten, H., Symmetric random walks on groups, Trans. Amer. Math. Soc. 92 (1959) 336–354, Theorem 3 and Lemma 2.2, https://doi.org/10.1090/S0002-9947-1959-0109367-6

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem norm_adjFree (d : ℕ) (hd : 1 ≤ d) :
    ‖adjFree d‖ = 2 * Real.sqrt (2 * d - 1) := by
  sorry

end StrongConv
