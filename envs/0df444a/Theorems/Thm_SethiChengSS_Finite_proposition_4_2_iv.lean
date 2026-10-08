-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_2_iv
-- name    : SethiChengSS.Finite.proposition_4_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:57.464027+00:00
-- url     : https://prove2.me/theorems/47aa97fe-b1b6-47d2-b1a1-aaf6b3e5b9fa
-- title:
--   Proposition 4.2(iv), p. 934 — h is K-convex on (−∞, B]
-- statement:
--   Under the hypotheses of Proposition 4.2, let $K \ge 0$ and let $g$ be a $K$-convex, lower semicontinuous function with $g(x) \to +\infty$ as $x \to +\infty$. Let $A \le B$ be extended reals, $A \ne +\infty$, $B \ne -\infty$, with $g^* = \inf_{A\le x\le B} g(x) > -\infty$. Then the function
--   $$h(x) = \inf_{y \ge x,\ A \le y \le B}\,[K\delta(y-x) + g(y)]$$
--   is $K$-convex on $(-\infty, B]$ in the sense of Definition 4.2.
--
--   This is what propagates $K$-convexity backwards through the dynamic programming recursion: in the proof of Theorem 4.1, $h_n$ is $K^i_n$-convex, and so is $v_n = f_n - c^i_n x + h_n$.
--
--   **Formalization Note** $h$ is `EReal`-valued in Lean and is converted to a real function; by Proposition 4.2(iii) it is finite on $(-\infty, B]$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.2(iv); proof p. 935

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.2(iv) (Sethi–Cheng 1997, p. 934): under the hypotheses of Proposition 4.2, the
function `h(x) = inf_{y ≥ x, A ≤ y ≤ B} [K δ(y − x) + g(y)]` is `K`-convex on `(−∞, B]`. -/
theorem proposition_4_2_iv (K : ℝ) (g : ℝ → ℝ) (A B : EReal) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hlsc : LowerSemicontinuous g)
    (hcoer : Tendsto g atTop atTop) (hAB : A ≤ B) (hA : A ≠ ⊤) (hB : B ≠ ⊥)
    (hstar : gStar g A B ≠ ⊥) :
    KConvexOn K (IicE B) (fun x => (hFun g K A B x).toReal) := by sorry

end SethiChengSS.Finite
