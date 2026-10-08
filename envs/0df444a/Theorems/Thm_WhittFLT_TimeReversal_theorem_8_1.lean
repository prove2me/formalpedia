-- Prove2me | Theorems.Thm_WhittFLT_TimeReversal_theorem_8_1
-- name    : WhittFLT.TimeReversal.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:54.69556+00:00
-- url     : https://prove2.me/theorems/862bd853-b564-4092-bf57-335d6aa40ac7
-- title:
--   Theorem 8.1 — time reversal is a J₁ isometry and shifted reversal is 2-Lipschitz
-- statement:
--   Let $(S,m)$ be a complete separable additive metric group with translation-invariant metric, and let $D$ be the càdlàg paths on $[0,1]$ satisfying $x(1)=x(1-)$. For $x,y\in D$, with $d$ the Skorohod $J_1$ metric of (2.1),
--
--   $$
--   d(Rx,Ry)=d(x,y),\qquad d(rx,ry)\le 2d(x,y).
--   $$
--
--   Thus ordinary reversal preserves $J_1$ distance exactly, while reversal shifted to start at the identity changes it by at most a factor of two. The restriction of the second inequality to $D_\theta\times D_\theta$ follows because $D_\theta\subseteq D$.
--
--   **Formalization Note** The paper's metric group is represented by an additive commutative group and an explicit translation-invariance hypothesis. Lean paths are total functions whose values outside $[0,1]$ do not enter the metric. The terminal left-continuity condition is built into $D$, $R$ reads left limits, and $d$ takes values in $[0,\infty]$ to avoid default real suprema. The formula's constant is the printed $2$.
-- source:
--   Whitt, Some Useful Functions for Functional Limit Theorems, Math. Oper. Res. 5(1) (1980), Theorem 8.1, p. 83 and proof p. 84; https://doi.org/10.1287/moor.5.1.67

import Mathlib
import Definitions.Def_WhittFLT_TimeReversal_Reversal

namespace WhittFLT.TimeReversal

/-- Whitt, Theorem 8.1, p. 83: time reversal is a J₁ isometry; centered reversal is 2-Lipschitz. -/
theorem theorem_8_1 {S : Type*} [AddCommGroup S] [MetricSpace S] [CompleteSpace S]
    [TopologicalSpace.SeparableSpace S] (hinv : ∀ a b c : S, dist (a + c) (b + c) = dist a b)
    (x y : ℝ → S) (hx : InD x) (hy : InD y) :
    WhittFLT.Composition.j1Dist 0 1 (revTime x) (revTime y) = WhittFLT.Composition.j1Dist 0 1 x y ∧
      WhittFLT.Composition.j1Dist 0 1 (revTime0 x) (revTime0 y) ≤ 2 * WhittFLT.Composition.j1Dist 0 1 x y := by sorry

end WhittFLT.TimeReversal
