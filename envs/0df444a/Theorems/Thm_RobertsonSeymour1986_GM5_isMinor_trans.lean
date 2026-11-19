-- Prove2me | Theorems.Thm_RobertsonSeymour1986_GM5_isMinor_trans
-- name    : RobertsonSeymour1986.GM5.isMinor_trans
-- status  : Proved
-- author  : @Davide
-- created : 2026-11-18T12:50:18.906191+00:00
-- url     : https://prove2.me/theorems/824e9e9d-5c89-4434-b6f7-a7ae29f3f461
-- title:
--   A minor of a minor is a minor
-- statement:
--   The minor relation is transitive: if $H$ is a minor of $K$ and $K$ is a minor of $G$, then $H$ is a minor of $G$:
--
--   $$H\preceq K\ \text{ and }\ K\preceq G\quad\Longrightarrow\quad H\preceq G.$$
--
--   In the branch-set model, if $(\beta_1(w))_{w\in V(H)}$ models $H$ in $K$ and $(\beta_2(u))_{u\in V(K)}$ models $K$ in $G$, then $w\mapsto\bigcup_{u\in\beta_1(w)}\beta_2(u)$ models $H$ in $G$. Transitivity is used throughout Graph Minors V, for instance to pass from 'no $H$ minor' to 'no grid minor' when $H$ is a minor of a grid.
--
--   **Formalization Note** Minors are `IsMinor` (branch-set model) on arbitrary vertex types.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 1, p. 92 (definition of minor: 'obtained by contraction from a subgraph'); transitivity of the minor relation is implicit there and standard.

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace RobertsonSeymour1986.GM5
theorem isMinor_trans {W U V : Type} {H : SimpleGraph W} {K : SimpleGraph U} {G : SimpleGraph V}
    (hHK : IsMinor H K) (hKG : IsMinor K G) : IsMinor H G := by sorry
end RobertsonSeymour1986.GM5
