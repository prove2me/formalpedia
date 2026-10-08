-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_eq_4_11_minimizer
-- name    : PenaltyLag.Asymptotic.eq_4_11_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:46.125858+00:00
-- url     : https://prove2.me/theorems/c33879c9-99a6-4022-b35a-ac66d7710e70
-- title:
--   Proof of Theorem 4.1, (4.9)–(4.11) — the unique minimizer of $u \mapsto F_0(x,u) + u\cdot y + r|u|^2$ is $\nabla_y L_r(x,y)$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Let $r > 0$, $x \in X$ and $y \in \mathbb R^m$, and let $F_0$ be the function (3.4) for $r = 0$: $F_0(x, u) = f_0(x)$ if $u_i \ge f_i(x)$ for all $i$, and $+\infty$ otherwise. Then the function
--   $$
--   u \;\mapsto\; F_0(x, u) + u \cdot y + r|u|^2
--   $$
--   attains its minimum over $\mathbb R^m$ at a unique point, this minimum equals $L_r(x, y)$ (4.9), and the minimizing point is
--   $$
--   u = \nabla_y L_r(x, y). \tag{4.11}
--   $$
--
--   In the proof of Theorem 4.1 this identifies the "constraint slack" vector $u^k$ with the inexact dual gradient, which Lemmas 4.2 and 4.3 drive to $0$.
--
--   **Formalization Note** The paper states this for the iterates $x^k$, $y^k$; it holds for every $x \in X$, $y$, and is stated so. The three claims (minimality, value $L_r(x, y)$, uniqueness) are separate conjuncts; values are in `EReal` since $F_0$ takes $+\infty$. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 366, proof of Theorem 4.1, (4.9)–(4.11)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Proof of Theorem 4.1, (4.9)–(4.11) (p. 366): for r > 0, x ∈ X and y ∈ ℝ^m, the function
u ↦ F₀(x, u) + u·y + r|u|² attains its minimum L_r(x, y) at a unique point, namely ∇_y L_r(x, y). -/
theorem eq_4_11_minimizer {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (x : E) (hx : x ∈ X) (y : Mult m) :
    (∀ v : Mult m,
      Fr f₀ f 0 x (gradient (fun y' : Mult m => Lr f₀ f r x y') y)
          + ((inner ℝ (gradient (fun y' : Mult m => Lr f₀ f r x y') y) y
              + r * ‖gradient (fun y' : Mult m => Lr f₀ f r x y') y‖ ^ 2 : ℝ) : EReal)
        ≤ Fr f₀ f 0 x v + ((inner ℝ v y + r * ‖v‖ ^ 2 : ℝ) : EReal)) ∧
    Fr f₀ f 0 x (gradient (fun y' : Mult m => Lr f₀ f r x y') y)
          + ((inner ℝ (gradient (fun y' : Mult m => Lr f₀ f r x y') y) y
              + r * ‖gradient (fun y' : Mult m => Lr f₀ f r x y') y‖ ^ 2 : ℝ) : EReal)
        = (Lr f₀ f r x y : EReal) ∧
    ∀ u : Mult m,
      (∀ v : Mult m, Fr f₀ f 0 x u + ((inner ℝ u y + r * ‖u‖ ^ 2 : ℝ) : EReal)
          ≤ Fr f₀ f 0 x v + ((inner ℝ v y + r * ‖v‖ ^ 2 : ℝ) : EReal)) →
      u = gradient (fun y' : Mult m => Lr f₀ f r x y') y := by sorry

end PenaltyLag.Asymptotic
