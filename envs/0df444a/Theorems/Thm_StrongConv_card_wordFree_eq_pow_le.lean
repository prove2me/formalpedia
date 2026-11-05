-- Prove2me | Theorems.Thm_StrongConv_card_wordFree_eq_pow_le
-- name    : StrongConv.card_wordFree_eq_pow_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:50:32.075195+00:00
-- url     : https://prove2.me/theorems/c893f206-416b-4cbb-96ea-895152714538
-- title:
--   Lemma 8.3 — Friedman's bound on words reducing to a proper power
-- statement:
--   For every $d$, $k \ge 2$ and $p \ge 1$, the number of pairs $(i_1, \dots, i_p;\ v)$, with each $i_j$ one of the $2d$ letters $g_1, \dots, g_d, g_1^{-1}, \dots, g_d^{-1}$ and $v \in \mathbf F_d$ a non-power such that $g_{i_1}\cdots g_{i_p} = v^k$, is at most $(p + 1)^4\,\|A_{\rm F}\|^p$, where $A_{\rm F}$ is the adjacency operator of the $2d$-regular tree on $l^2(\mathbf F_d)$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), pp. 24–25, Lemma 8.3

import Mathlib
import Definitions.Def_StrongConv

namespace StrongConv

theorem card_wordFree_eq_pow_le (d k p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p) :
    (Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} : ℝ) ≤
      ((p : ℝ) + 1) ^ 4 * ‖adjFree d‖ ^ p := by
  sorry

end StrongConv
