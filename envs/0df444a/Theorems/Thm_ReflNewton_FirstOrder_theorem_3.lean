-- Prove2me | Theorems.Thm_ReflNewton_FirstOrder_theorem_3
-- name    : ReflNewton.FirstOrder.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:53:59.238987+00:00
-- url     : https://prove2.me/theorems/0192ea16-cc00-4c61-ad67-3d0d687205c1
-- title:
--   Theorem 3, p. 203 — constraint compatibility keeps the matching breakpoints bounded away from zero
-- statement:
--   Let $\{x_k\}$ be interior points of the box, $l<x_k<u$, and let $\{s_k\}$ be constraint-compatible, i.e. $\{D_k^{-2}s_k\}$ is bounded, where $D_k^2=\operatorname{diag}(|v(x_k)|)$. Let $BR_k(j)$ be the positive distance along $s_k$ to the first bound in coordinate $j$, with value $+\infty$ if there is none. Then there is $c>0$ such that, for every iteration $k$ and index $j$,
--   $$BR_k(j)=\frac{|v_{kj}|}{|s_{kj}|}\quad\Longrightarrow\quad BR_k(j)\ge c.$$
--
--   These are the breakpoints of (3.1) for variables moving towards the bound measured by $v$ (the "correct sign condition"). This is the ingredient of Lemma 7 that rules out short steps into such a bound.
--
--   **Formalization Note** The breakpoint is computed from the finite bound in the direction of motion; an absent bound or zero direction gives $+\infty$. This is (3.1) with its infinity rules, specialized to interior iterates. The interiority hypothesis makes $v_{kj}\neq0$, so $D_k^{-2}$ is a genuine inverse.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), p. 203, Theorem 3

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_ReflNewton_FirstOrder_Setting
open Filter Topology

namespace ReflNewton.FirstOrder

theorem theorem_3 {n : ℕ} (l u : Fin n → EReal) (f : E n → ℝ) (x s : ℕ → E n)
    (hx : ∀ k, x k ∈ intBox l u) (hcc : IsConstraintCompatible l u f x s) :
    let br : ℕ → Fin n → EReal := fun k j =>
      if 0 < s k j then
        if u j = ⊤ then ⊤ else (((u j).toReal - x k j) / s k j : ℝ)
      else if s k j < 0 then
        if l j = ⊥ then ⊤ else (((l j).toReal - x k j) / s k j : ℝ)
      else ⊤
    ∃ c : ℝ, 0 < c ∧ ∀ k j,
      br k j = ((|vVec l u f (x k) j| / |s k j| : ℝ) : EReal) →
        (c : EReal) ≤ br k j := by sorry

end ReflNewton.FirstOrder
