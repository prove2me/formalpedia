-- Prove2me | Theorems.Thm_ReflectedBSDE_Existence_lemma_2_1
-- name    : ReflectedBSDE.Existence.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:49.31893+00:00
-- url     : https://prove2.me/theorems/30d71f51-1272-47ee-ac02-11eba198694a
-- title:
--   Lemma 2.1 — the Skorohod problem has a unique solution, with $k_t=\sup_{s\le t}x_s^-$
-- statement:
--   Let $x:[0,\infty)\to\mathbb R$ be continuous with $x_0\ge 0$. Then there is exactly one pair $(y,k)$ of functions on $[0,\infty)$ such that
--
--   1. $y=x+k$;
--   2. $y_t\ge0$ for every $t$;
--   3. $k$ is continuous and nondecreasing, $k_0=0$, and $\int_0^\infty y_t\,dk_t=0$.
--
--   This pair is the solution of the Skorohod problem. Moreover, for every $t\ge0$,
--   $$k_t=\sup_{s\le t}x_s^-,$$
--   where $x^-=\max(-x,0)$.
--
--   The lemma identifies the minimal reflecting push in closed form. The paper applies it pathwise, in reversed time, to express the increasing process of a reflected BSDE as a running supremum (Proposition 2.2).
--
--   **Formalization Note** $\int_0^\infty y\,dk$ is the lower Lebesgue integral of $y$ against the Stieltjes measure of $k$, from the definition `ReflectedBSDE.Existence.Skorohod`. The paper recalls the lemma from the literature (its references [11] and [20]) without proof.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 704–705 (PDF pp. 3–4), Lemma 2.1

import Mathlib
import Definitions.Def_ReflectedBSDE_Existence_Skorohod

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedBSDE.Existence

/-- Lemma 2.1 (the Skorohod lemma, pp. 704–705): for a continuous `x : [0, ∞[ → ℝ` with
`x_0 ≥ 0` there is exactly one pair `(y, k)` solving the Skorohod problem, and its `k` is
`k_t = sup_{s≤t} x_s⁻`. -/
theorem lemma_2_1 (x : ℝ≥0 → ℝ) (hx : Continuous x) (hx0 : 0 ≤ x 0) :
    (∃! p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ), IsSkorohodSolution x p.1 p.2) ∧
    ∀ y k : ℝ≥0 → ℝ, IsSkorohodSolution x y k →
      ∀ t, k t = ⨆ s : Iic t, max (-(x s)) 0 := by sorry

end ReflectedBSDE.Existence
