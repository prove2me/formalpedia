-- Prove2me | Theorems.Thm_RankOneSK_theorem_3_1
-- name    : RankOneSK.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:30.50112+00:00
-- url     : https://prove2.me/theorems/b2894517-4dfc-447a-8903-527e2c3d642e
-- title:
--   Theorem 3.1 — Main Technical Lemma: the local rank-one-perturbed form is nonnegative for $|J|\le j(d,\lambda,s)$, uniformly in the fields
-- statement:
--   Let $\mu_{J,a,b}$ be the two-spin Ising measure, $L_Xf=f-\mathbb E[f\mid Y]$, $L_Yf=f-\mathbb E[f\mid X]$, $\bar X(y)=\mathbb E[X\mid y]$, $\bar Y(x)=\mathbb E[Y\mid x]$ and $M(x,y)=(x+s\bar X(y))(y+s\bar Y(x))$; all expectations are under $\mu_{J,a,b}$.
--
--   **Theorem 3.1.** Let $d,s\le1$ and $\lambda>0$ satisfy
--   $$d\ \ge\ \max\{-(s^2+2s-1),\,2s^2\}.\tag{24}$$
--   Then there is $j=j(d,\lambda,s)>0$ such that for every $J$ with $|J|\le j$, all $a,b\in\mathbb R$ and all $f:\{\pm1\}^2\to\mathbb R$,
--   $$\mathbb E[(L_Xf)(L_Yf)]+J\,\mathbb E[M(L_Xf)(L_Yf)]+\frac{(\lambda J)^2}2\mathbb E[(L_Xf)^2+(L_Yf)^2]+\frac{dJ^2}2\mathbb E\big[\bar X(y)^2(L_Xf)^2+\bar Y(x)^2(L_Yf)^2\big]\ \ge\ 0 .$$
--
--   Applied to the conditional law of two spins of the SK model given all others, it gives the local inequality (25); the threshold $j$ does not depend on the external fields $a,b$, which is what allows averaging over the other spins.
--
--   Differences from the source:
--   - encoding: f : {±1}² → ℝ and the displayed expression → f : Bool → Bool → ℝ and localForm d s λ J a b f; reason: Lean convention; same expression
--   - encoding: "there exists j(d, λ, s) > 0" → ∃ j > 0 after d, s, λ and before J, a, b, f; reason: j depends only on d, λ, s
--   - encoding: x, y ∈ {±1}; expectations under µ_{J,a,b} → Bool spins read as ±1; twoSpinExp J a b; reason: Lean convention; same objects
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 3.1 and (24), p.19 (PDF p.20)

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_localForm

open OAI.SKGap MeasureTheory ProbabilityTheory Filter

namespace RankOneSK

/-- **Theorem 3.1 (Main Technical Lemma).** Let `d, s ⩽ 1` and `λ > 0` be such that
`d ⩾ max{−(s² + 2s − 1), 2s²}` (24). Then there exists `j(d, λ, s) > 0` such that for all `J` with
`|J| ⩽ j(d, λ, s)`, all `a, b ∈ ℝ` and all `f : {±1}² → ℝ`,
`E[(L_X f)(L_Y f)] + J·E[M(L_X f)(L_Y f)] + ((λJ)²/2)·E[(L_X f)² + (L_Y f)²]
  + (dJ²/2)·E[X̄(y)²·L_X f(x, y)² + Ȳ(x)²·L_Y f(x, y)²] ⩾ 0`,
with `M(x, y) = (x + sX̄(y))(y + sȲ(x))` and all expectations under `µ_{J,a,b}`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 3.1 and (24), p.19.

**Formalization Note** Two-spin objects: spins are `Bool` read as ±1 by `spinValue`; `twoSpinExp J a b` is
`E_{µ_{J,a,b}}` and `twoSpinExp 0 a b` is `E_{µ_{0,a,b}}`. `J` is the raw interaction. The left side is
`localForm d s lam J a b f`. `j` is chosen after `d, s, λ` and before `J, a, b, f`: it does not depend on
the fields. -/
theorem theorem_3_1 :
    ∀ d s lam : ℝ, d ≤ 1 → s ≤ 1 → 0 < lam →
      max (-(s ^ 2 + 2 * s - 1)) (2 * s ^ 2) ≤ d →
      ∃ j : ℝ, 0 < j ∧ ∀ J : ℝ, |J| ≤ j → ∀ a b : ℝ, ∀ f : Bool → Bool → ℝ,
        0 ≤ localForm d s lam J a b f := by sorry

end RankOneSK
