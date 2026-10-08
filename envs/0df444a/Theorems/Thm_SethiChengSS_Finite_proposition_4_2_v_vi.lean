-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_2_v_vi
-- name    : SethiChengSS.Finite.proposition_4_2_v_vi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:06.95476+00:00
-- url     : https://prove2.me/theorems/32aa8fd9-fdb2-490a-af5a-f56c88ce3cec
-- title:
--   Proposition 4.2(v)–(vi), p. 934 — if s > A: s is real, g is strictly decreasing on (A, s], and g(s) = K + g(S) for continuous g
-- statement:
--   Under the hypotheses of Proposition 4.2, let $K \ge 0$ and let $g$ be $K$-convex and lower semicontinuous with $g(x)\to+\infty$ as $x\to+\infty$. Let $A \le B$ be extended reals ($A \ne +\infty$, $B \ne -\infty$) with $g^* > -\infty$, and let $S$, $s$ be given by (4.5)–(4.6). Suppose $s > A$. Then:
--   1. $s$ is a real number;
--   2. (vi) $g$ is strictly decreasing on $(A, s]$;
--   3. (v) if moreover $g$ is continuous, then
--   $$g(s) = K + g(S).$$
--
--   So when $s$ is finite and an order is ever worthwhile, the reorder point $s$ sits exactly where the cost exceeds the minimum by the fixed cost $K$.
--
--   **Formalization Note** The paper states (v) for lower semicontinuous $g$; the continuity hypothesis on (v) is added because the printed claim is false without it. Take $K = 1$, $A = -\infty$, $B = +\infty$, and $g(x) = 1 - x$ for $x < 0$, $g(x) = (1-x)/2$ on $[0,1]$, $g(x) = x - 1$ for $x > 1$. This $g$ is $1$-convex, lower semicontinuous and coercive at $+\infty$, with $S = 1$ and $s = 0$, but $g(s) = 1/2 < K + g(S) = 1$. The inequality $g(s) \le K + g(S)$ always holds; it is part of Proposition 4.2(i)–(iii) in this mission. In the paper's application $g = z_n(i,\cdot)$ is continuous. Item (vi) is stated for lower semicontinuous $g$, as printed.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.2(v)–(vi) and proof

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.2(v)–(vi) (Sethi–Cheng 1997, p. 934), corrected. Under the hypotheses of
Proposition 4.2, if `s > A` then `s` is a real number, (vi) `g` is strictly decreasing on
`(A, s]`, and (v) `g(s) = K + g(S)` provided `g` is continuous. The continuity hypothesis on (v)
is added: for a merely lower semicontinuous `g` the printed (v) fails (`K = 1`, `g(x) = 1 − x`
for `x < 0`, `g(x) = (1 − x)/2` on `[0, 1]`, `g(x) = x − 1` for `x > 1`, `A = −∞`, `B = +∞`:
then `S = 1`, `s = 0` and `g(s) = 1/2 < K + g(S) = 1`); in the paper's application `g = z_n`
is continuous. -/
theorem proposition_4_2_v_vi (K : ℝ) (g : ℝ → ℝ) (A B : EReal) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hlsc : LowerSemicontinuous g)
    (hcoer : Tendsto g atTop atTop) (hAB : A ≤ B) (hA : A ≠ ⊤) (hB : B ≠ ⊥)
    (hstar : gStar g A B ≠ ⊥) (hsA : A < smallS g K A B) :
    (smallS g K A B ≠ ⊥ ∧ smallS g K A B ≠ ⊤) ∧
    (Continuous g → gExt g (smallS g K A B) = (K : EReal) + gExt g (bigS g A B)) ∧
    StrictAntiOn g {x : ℝ | A < (x : EReal) ∧ (x : EReal) ≤ smallS g K A B} := by sorry

end SethiChengSS.Finite
