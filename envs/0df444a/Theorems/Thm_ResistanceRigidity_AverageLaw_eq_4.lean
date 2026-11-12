-- Prove2me | Theorems.Thm_ResistanceRigidity_AverageLaw_eq_4
-- name    : ResistanceRigidity.AverageLaw.eq_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T23:06:36.981195+00:00
-- url     : https://prove2.me/theorems/504efee1-be62-43f9-9cf7-79f2286ff291
-- title:
--   §2, eq. (4) — the local identity $1/\delta_u = a_u - t_u/2$ (with $c_u = \delta_u a_u$)
-- statement:
--   Let $G$ be a connected weighted graph on a finite vertex set $V$ with $N \ge 2$ vertices and conductance function $c$ (symmetric, nonnegative, zero on the diagonal), with effective resistances $R_{uv}$ and weighted degrees $\delta_u = \sum_x c(u,x)$. Fix a vertex $u$, let $p_v = c(u,v)/\delta_u$, and set
--   $$a_u = \sum_v p_v R_{uv}, \qquad t_u = \sum_{v,x} p_v p_x R_{vx}, \qquad c_u = \sum_v c(u,v) R_{uv}.$$
--   Then $c_u = \delta_u a_u$ and
--   $$\frac1{\delta_u} = a_u - \frac{t_u}{2}.$$
--
--   This is the local identity of the paper (equivalent to an expression of Devriendt and Lambiotte). Combined with the bound $t_u \le \max R\,(1 - \sum_v p_v^2)$ it caps $c_u$ by a function of the support degree (eq. (7)), which drives the proof of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: a graph with positive edge conductances $w$, $w_{uv} = 0$ off the edges and on the diagonal → a conductance function $c : V \to V \to \mathbb R$ that is symmetric, nonnegative and zero on the diagonal, edges being the pairs with $c > 0$; reason: the same weighted graphs.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 6, §2, eq. (4)

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Local

namespace ResistanceRigidity.AverageLaw

/-- §2, eq. (4), the local identity: at every vertex `u` of a connected weighted graph with at
least two vertices, `c_u = δ_u a_u` and `1/δ_u = a_u − t_u/2`. -/
theorem eq_4 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 2 ≤ Fintype.card V) (u : V) :
    IncrementalER.levDeg c u = IncrementalER.capDeg c u * avgRes c u ∧
      1 / IncrementalER.capDeg c u = avgRes c u - pairRes c u / 2 := by sorry

end ResistanceRigidity.AverageLaw
