-- Prove2me | Theorems.Thm_RandomOrderCRS_proposition_8
-- name    : RandomOrderCRS.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:07.482401+00:00
-- url     : https://prove2.me/theorems/41528000-9993-41f9-8b69-ce175f50ed7d
-- title:
--   Proposition 8 — first-order minimization properties of $a_1$
-- statement:
--   For $a=a_1$: for all $y\in[0,1]$, the function $x\mapsto\ln(1-y\,x\,a(x))$ is convex on $[0,1]$. Moreover, $a(0)=1$, and $a$ is continuous and decreasing on $[0,1]$.
--
--   These analytic properties drive the worst-case analysis in Lemma 2.
--
--   Differences from the source:
--   - reading: $a$ is decreasing → strictly decreasing (`StrictAntiOn`); reason: the stronger of the two readings; it holds for $a_1$
--   - encoding: the function is convex → convex on $[0,1]$ (`ConvexOn ℝ (Set.Icc 0 1)`); reason: $[0,1]$ is the domain of $a$
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Proposition 8, p.20; §C.3, ec16

import Mathlib
import Definitions.Def_RandomOrderCRS_Attenuation

open Real

namespace RandomOrderCRS

/-- Proposition 8 (First-order minimization), MacRury, Ma & Grammel, arXiv:2209.07520v2, p.20, for
`a = a₁` (§C.3, ec16): "For all y ∈ [0, 1], the function x → ln(1 − y x a(x)) is convex. Moreover,
a(0) = 1, and a is continuous and decreasing on [0, 1]."

**Formalization Note.** Convexity is on `[0, 1]`, the domain of `a`. "Decreasing" is read as strictly
decreasing, which is the stronger reading and holds for `a₁`. -/
theorem proposition_8 :
    (∀ y ∈ Set.Icc (0 : ℝ) 1, ConvexOn ℝ (Set.Icc (0 : ℝ) 1) fun t => log (1 - y * t * a₁ t)) ∧
    a₁ 0 = 1 ∧ ContinuousOn a₁ (Set.Icc (0 : ℝ) 1) ∧ StrictAntiOn a₁ (Set.Icc (0 : ℝ) 1) := by sorry

end RandomOrderCRS
