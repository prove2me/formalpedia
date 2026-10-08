-- Prove2me | Theorems.Thm_SethiChengSS_Finite_proposition_4_2_i_iii
-- name    : SethiChengSS.Finite.proposition_4_2_i_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:59.394751+00:00
-- url     : https://prove2.me/theorems/6037ff44-5807-4b56-bbb2-dee566c05990
-- title:
--   Proposition 4.2(i)–(iii), p. 934 — S and s are attained, g ≥ g(S) on [A, B], g(x) ≤ g(y) + K for s ≤ x ≤ y ≤ B, and the form of h
-- statement:
--   Let $K \ge 0$ and let $g:\mathbb R \to \mathbb R$ be $K$-convex and lower semicontinuous with $g(x) \to +\infty$ as $x \to +\infty$. Let $A \le B$ be extended real numbers with $A \ne +\infty$ and $B \ne -\infty$; the interval $[A,B]$ is open at an infinite endpoint. Write $g(-\infty) = \liminf_{x\to-\infty} g(x)$ and assume
--   $$g^* = \inf_{A \le x \le B} g(x) > -\infty. \qquad (4.4)$$
--   Let $S$ and $s$ be the smallest points of $\mathbb R \cup \{-\infty\}$ with $g(S) = g^*$, $A \le S \le B$ (4.5) and with $g(s) \le K + g(S)$, $A \le s \le S$ (4.6). Then:
--
--   0. both minima are attained, so $S < +\infty$, $A \le s \le S \le B$, $g(S) = g^*$ and $g(s) \le K + g(S)$;
--   1. (i) $g(x) \ge g(S)$ for every real $x \in [A,B]$;
--   2. (ii) $g(x) \le g(y) + K$ whenever $s \le x \le y \le B$;
--   3. (iii) for real $x \le B$,
--   $$h(x) \equiv \inf_{y \ge x,\ A \le y \le B}\,[K\delta(y-x) + g(y)] = \begin{cases} K + g(S), & x < s,\\ g(x), & s \le x \le B,\end{cases}$$
--   so $h$ is real valued on $(-\infty, B]$; moreover $h$ is lower semicontinuous on $(-\infty, B]$, and if $g$ is continuous, $A = -\infty$ and $B = +\infty$, then $h$ is continuous on $\mathbb R$.
--
--   This is the one-period $(s,S)$ structure: from level $x$ it is optimal to move to $S$ when $x < s$ and to stay otherwise. It extends Lemma (d) of Bertsekas (1978) to a lower semicontinuous $g$, a bounded interval $[A,B]$, and possibly infinite $s$ and $S$ (Remark 4.4).
--
--   **Formalization Note**
--   1. $A$, $B$, $s$, $S$, $g^*$ and $h$ live in the extended reals.
--   2. $A \ne +\infty$ and $B \ne -\infty$ exclude an empty interval, which the paper does not consider.
--   3. Item 0 is the "min" of (4.5)–(4.6): the definitions take infima, and the statement asserts that they are attained.
--   4. "$h$ is l.s.c." is stated for the real-valued $h$ on $\{x : x \le B\}$.
-- source:
--   Sethi and Cheng, Optimality of (s, S) policies in inventory models with Markovian demand, Oper. Res. 45(6) (1997), DOI 10.1287/opre.45.6.931, p. 934, Proposition 4.2 (4.4)–(4.6) and (i)–(iii); proof pp. 934–935

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_SethiChengSS_Finite_KConvexity
open MeasureTheory Filter Topology

namespace SethiChengSS.Finite

/-- Proposition 4.2 (0)–(iii) (Sethi–Cheng 1997, p. 934). Let `g` be `K`-convex, lower
semicontinuous, with `g(x) → +∞` as `x → +∞`; let `A ≤ B` be extended reals (`A ≠ +∞`,
`B ≠ −∞`) with `g* = inf_{A ≤ x ≤ B} g(x) > −∞` (4.4); let `S`, `s` be given by (4.5), (4.6).
Then (0) the minima in (4.5) and (4.6) are attained; (i) `g(x) ≥ g(S)` on `[A, B]`;
(ii) `g(x) ≤ g(y) + K` for `s ≤ x ≤ y ≤ B`; (iii) `h(x) = K + g(S)` for `x < s` and `h(x) = g(x)`
for `s ≤ x ≤ B`, `h` is real valued and l.s.c. on `(−∞, B]`, and `h` is continuous on `ℝ` when
`g` is continuous, `A = −∞`, `B = +∞`. -/
theorem proposition_4_2_i_iii (K : ℝ) (g : ℝ → ℝ) (A B : EReal) (hK : 0 ≤ K)
    (hg : BertsekasKConvex K g) (hlsc : LowerSemicontinuous g)
    (hcoer : Tendsto g atTop atTop) (hAB : A ≤ B) (hA : A ≠ ⊤) (hB : B ≠ ⊥)
    (hstar : gStar g A B ≠ ⊥) :
    (bigS g A B ≠ ⊤ ∧ A ≤ bigS g A B ∧ bigS g A B ≤ B ∧ gExt g (bigS g A B) = gStar g A B) ∧
    (smallS g K A B ≠ ⊤ ∧ A ≤ smallS g K A B ∧ smallS g K A B ≤ bigS g A B ∧
      gExt g (smallS g K A B) ≤ (K : EReal) + gExt g (bigS g A B)) ∧
    (∀ x : ℝ, x ∈ IccE A B → gExt g (bigS g A B) ≤ (g x : EReal)) ∧
    (∀ x y : ℝ, smallS g K A B ≤ (x : EReal) → x ≤ y → (y : EReal) ≤ B → g x ≤ g y + K) ∧
    (∀ x : ℝ, (x : EReal) ≤ B →
      hFun g K A B x =
        if (x : EReal) < smallS g K A B then (K : EReal) + gExt g (bigS g A B)
        else (g x : EReal)) ∧
    (∀ x : ℝ, (x : EReal) ≤ B → hFun g K A B x ≠ ⊥ ∧ hFun g K A B x ≠ ⊤) ∧
    LowerSemicontinuousOn (fun x => (hFun g K A B x).toReal) (IicE B) ∧
    (Continuous g → A = ⊥ → B = ⊤ → Continuous (fun x => (hFun g K A B x).toReal)) := by sorry

end SethiChengSS.Finite
