-- Prove2me | Theorems.Thm_ResistanceRigidity_AverageLaw_eq_7
-- name    : ResistanceRigidity.AverageLaw.eq_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T23:06:26.609403+00:00
-- url     : https://prove2.me/theorems/3e57909d-6591-48ee-a95f-7c39c31722ca
-- title:
--   §3, eq. (7) — for $\varepsilon < 1$, $c_u \le 1/(1 - \tfrac12(1+\varepsilon)(1 - 1/k_u)) = f(k_u)$
-- statement:
--   Let $G$ be a connected weighted graph on a finite vertex set $V$ with $N \ge 3$ vertices and conductance function $c$ (symmetric, nonnegative, zero on the diagonal), with effective resistances $R_{uv}$ and spread
--   $$\varepsilon = \frac{\max_{u\ne v} R_{uv}}{\min_{u \ne v} R_{uv}} - 1 .$$
--   Assume $\varepsilon < 1$. For a vertex $u$ let $k_u$ be its number of neighbours and $c_u = \sum_v c(u,v) R_{uv}$. Then
--   $$c_u \le \frac{1}{1 - \frac12(1+\varepsilon)(1 - 1/k_u)} = f(k_u), \qquad f(x) = \frac{2x}{(1-\varepsilon)x + 1 + \varepsilon}.$$
--
--   This pointwise cap on $c_u$ in terms of the support degree is the step of the proof of Theorem 3.1 that, combined with $\sum_u c_u = 2(N-1)$ and Jensen's inequality for the concave $f$, yields the lower bound (6).
--
--   Differences from the source:
--   - encoding: a graph with positive edge conductances $w$, $w_{uv} = 0$ off the edges and on the diagonal → a conductance function $c : V \to V \to \mathbb R$ that is symmetric, nonnegative and zero on the diagonal, edges being the pairs with $c > 0$; reason: the same weighted graphs.
--   - encoding: stated after the normalization $\min_{u\ne v} R_{uv} = 1$ → stated without normalization; reason: $c_u$, $k_u$ and $\varepsilon$ do not change when all conductances are scaled by a positive constant, so the two statements are equivalent.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 6, §3, proof of Theorem 3.1, eq. (7)

import Mathlib
import Definitions.Def_IncrementalER_lap
import Definitions.Def_ResistanceRigidity_AverageLaw_Spread

namespace ResistanceRigidity.AverageLaw

/-- §3, eq. (7): on a connected weighted graph with at least three vertices and spread `ε < 1`,
every vertex `u` with support degree `k_u` has
`c_u ≤ 1/(1 − (1/2)(1 + ε)(1 − 1/k_u)) = f(k_u)`, where `f(x) = 2x/((1 − ε)x + 1 + ε)`. -/
theorem eq_7 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc : IncrementalER.IsGraph c) (hconn : IncrementalER.Connected c)
    (hN : 3 ≤ Fintype.card V) (hε : spread c < 1) (u : V) :
    IncrementalER.levDeg c u ≤
        1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (IncrementalER.deg c u : ℝ))) ∧
      1 / (1 - (1 / 2 : ℝ) * (1 + spread c) * (1 - 1 / (IncrementalER.deg c u : ℝ))) =
        2 * (IncrementalER.deg c u : ℝ) /
          ((1 - spread c) * (IncrementalER.deg c u : ℝ) + 1 + spread c) := by sorry

end ResistanceRigidity.AverageLaw
