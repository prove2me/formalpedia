-- Prove2me | Theorems.Thm_SendSplit_Existence_extreme_circulation_iff_eq_zero
-- name    : SendSplit.Existence.extreme_circulation_iff_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:12:38.118924+00:00
-- url     : https://prove2.me/theorems/e00e8c72-2e7d-4d80-bdf4-c0f0237748e6
-- title:
--   Proof of Theorem 1, p. 639 — the null circulation is the unique extreme circulation
-- statement:
--   Let $G$ be a graph (arcs join distinct nodes) and $x$ a circulation in $G$. Then $x$ is extreme, i.e. its induced subgraph is a forest, if and only if
--
--   $$x = 0.$$
--
--   This is used in Theorem 1 to pass from 3° to 2°: an extreme minimum-cost circulation must be the null circulation.
--
--   **Formalization Note** Forests are over arcs: a nonzero circulation on a pair of antiparallel arcs $(i,j),(j,i)$ induces a 2-cycle and is not extreme.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, proof of Theorem 1

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

theorem extreme_circulation_iff_eq_zero {n : ℕ} (G : ArcGraph n) (x : Fin n → Fin n → ℝ)
    (hx : IsCirculation G x) :
    IsExtremeFlow G (fun _ => 0) x ↔ x = 0 := by sorry

end SendSplit.Existence
