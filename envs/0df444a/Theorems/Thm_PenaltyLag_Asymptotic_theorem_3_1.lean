-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_theorem_3_1
-- name    : PenaltyLag.Asymptotic.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:12.395328+00:00
-- url     : https://prove2.me/theorems/aecb1fd0-b143-4e1e-8ef0-238dedcb9f61
-- title:
--   Theorem 3.1 — $L_r(x,y) = \min_u \{F_r(x,u) + u\cdot y\}$; $F_r$ convex; $L_r$ convex in $x$, concave in $y$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). For every $r \ge 0$ and $x \in X$, $y \in \mathbb R^m$,
--   $$
--   L_r(x, y) = \min\{F_r(x, u) + u \cdot y : u \in \mathbb R^m\},
--   $$
--   where $F_r$ is the function (3.4), which is convex on $X \times \mathbb R^m$. Therefore $L_r(x, y)$ is convex in $x \in X$ and concave in $y \in \mathbb R^m$.
--
--   Precisely:
--   1. for $r > 0$ the minimum is attained and equals $L_r(x, y)$;
--   2. for $r = 0$, $L_0(x, y)$ (3.2) is the infimum over $u$, and this infimum is attained whenever $y \ge 0$ (for $y \not\ge 0$ it is $-\infty$);
--   3. for every $r \ge 0$ the epigraph $\{(x, u, t) : x \in X,\ F_r(x, u) \le t\}$ is convex;
--   4. for $r > 0$, $x \mapsto L_r(x, y)$ is convex on $X$ and $y \mapsto L_r(x, y)$ is concave on $\mathbb R^m$;
--   5. for $r = 0$, the epigraph of $x \mapsto L_0(x, y)$ over $X$ and the hypograph of $y \mapsto L_0(x, y)$ are convex.
--
--   The theorem says $L_r$ is a Lagrangian in the sense of perturbational duality theory, obtained by perturbing $f_i$ to $f_i - u_i$ and simultaneously $f_0$ to $f_0 + r|u|^2$.
--
--   **Formalization Note** The paper prints "concave in $y \in Y$"; $Y$ is a misprint for $\mathbb R^m$. Since $F_r$ and $L_0$ take the values $\pm\infty$, their convexity and concavity are stated through convex epigraphs and hypographs; for $r > 0$, $L_r$ is real and Mathlib's `ConvexOn`/`ConcaveOn` are used. The paper's "min" at $r = 0$ is read as an infimum attained when finite. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 358–359, Theorem 3.1, (3.3), (3.4)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Theorem 3.1 (pp. 358–359). L_r is the partial conjugate of F_r; F_r is convex; L_r is convex
in x ∈ X and concave in y ∈ ℝ^m (the cases r > 0 and r = 0 are stated separately). -/
theorem theorem_3_1 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i)) :
    (∀ r : ℝ, 0 < r → ∀ x ∈ X, ∀ y : Mult m,
      IsLeast (Set.range fun u : Mult m => Fr f₀ f r x u + ((inner ℝ u y : ℝ) : EReal))
        (Lr f₀ f r x y : EReal)) ∧
    (∀ x ∈ X, ∀ y : Mult m,
      L0 f₀ f x y = ⨅ u : Mult m, Fr f₀ f 0 x u + ((inner ℝ u y : ℝ) : EReal) ∧
      ((∀ i, 0 ≤ y i) → ∃ u : Mult m, L0 f₀ f x y = Fr f₀ f 0 x u + ((inner ℝ u y : ℝ) : EReal))) ∧
    (∀ r : ℝ, 0 ≤ r →
      Convex ℝ {p : (E × Mult m) × ℝ | p.1.1 ∈ X ∧ Fr f₀ f r p.1.1 p.1.2 ≤ (p.2 : EReal)}) ∧
    (∀ r : ℝ, 0 < r → ∀ y : Mult m, ConvexOn ℝ X (fun x => Lr f₀ f r x y)) ∧
    (∀ r : ℝ, 0 < r → ∀ x ∈ X, ConcaveOn ℝ Set.univ (fun y : Mult m => Lr f₀ f r x y)) ∧
    (∀ y : Mult m, Convex ℝ {p : E × ℝ | p.1 ∈ X ∧ L0 f₀ f p.1 y ≤ (p.2 : EReal)}) ∧
    (∀ x ∈ X, Convex ℝ {p : Mult m × ℝ | (p.2 : EReal) ≤ L0 f₀ f x p.1}) := by sorry

end PenaltyLag.Asymptotic
