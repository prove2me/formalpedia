-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_1_iv
-- name    : SethiChengSS.Finite.proposition_4_1_iv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:08.17699+00:00
-- url     : https://prove2.me/theorems/5532a34d-14f2-4739-a10d-2f8f9888db93
-- title:
--   Proposition 4.1(iv), p. 934 — the restriction of a K-convex function to a convex set is K-convex
-- statement:
--   Let $g:\mathbb R\to\mathbb R$ be $K$-convex, $K \ge 0$, and let $D \subseteq \mathbb R$ be convex. Then the restriction of $g$ to $D$ is $K$-convex on $D$ in the sense of Definition 4.2: the inequality
--   $$K + g(z+y) \ge g(y) + z\,\frac{g(y)-g(y-b)}{b}$$
--   holds whenever $z \ge 0$, $b > 0$ and $y+z$, $y$, $y-b \in D$.
--
--   The proof of Proposition 4.2(iv) uses this for the case $s = -\infty$, where $h = g$ on $(-\infty, B]$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.1(iv)

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.1(iv) (Sethi–Cheng 1997, p. 934): the restriction of a `K`-convex function to
any convex set `D ⊆ ℝ` is `K`-convex in the sense of Definition 4.2. -/
theorem proposition_4_1_iv (K : ℝ) (g : ℝ → ℝ) (D : Set ℝ) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hD : Convex ℝ D) : KConvexOn K D g := by sorry

end SethiChengSS.Finite
