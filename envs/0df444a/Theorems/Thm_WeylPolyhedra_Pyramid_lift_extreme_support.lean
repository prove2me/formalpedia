-- Prove2me | Theorems.Thm_WeylPolyhedra_Pyramid_lift_extreme_support
-- name    : WeylPolyhedra.Pyramid.lift_extreme_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:16:43.613206+00:00
-- url     : https://prove2.me/theorems/afe9dcc1-7fdf-4015-8f5f-1d06e09dc184
-- title:
--   §2 a), p. 293 — an extreme support of the face system $S_0$ lifts to an extreme support (6) of $S$
-- statement:
--   Let $n = m + 1 \ge 2$ and let $S \subset \mathbb{R}^n$ be a finite non-degenerate point system for which the coordinate half-space $x_n \ge 0$ is an extreme support. Split $S$ into
--
--   1. $S_0$, the points of $S$ with $x_n = 0$, regarded as points $(x_1, \ldots, x_{n-1})$ of $\mathbb{R}^{n-1}$, and
--   2. $S'$, the remaining points of $S$ (those with $x_n \neq 0$, hence $x_n > 0$).
--
--   Let $\beta = (\beta_1, \ldots, \beta_{n-1})$ define an extreme support of $S_0$ in $\mathbb{R}^{n-1}$ (inequality (5)), and let $\mu$ be the minimum of
--
--   $$\frac{\beta_1 x_1 + \cdots + \beta_{n-1} x_{n-1}}{x_n}$$
--
--   over the points $x \in S'$, attained at some $a \in S'$. Then the inequality
--
--   $$\beta_1 x_1 + \cdots + \beta_{n-1} x_{n-1} - \mu\, x_n \ge 0 \tag{6}$$
--
--   is an extreme support of $S$.
--
--   This is the induction step of the proof of the Hauptsatz: a point $q$ on the plane $x_n = 0$ that satisfies every extreme support of $S$ then satisfies every extreme support of $S_0$, so the Hauptsatz in dimension $n-1$ applies to it.
--
--   **Formalization Note** The statement is in the coordinates Weyl fixes on p. 293 ("Man kann annehmen, daß die Gleichung $(\alpha x) = 0$ die Gestalt hat: $x_n = 0$"): points of $\mathbb{R}^n$ are functions $\mathrm{Fin}(m+1) \to \mathbb{R}$, $x_n$ is the coordinate `Fin.last m`, the projection to $\mathbb{R}^{n-1}$ is `Fin.init`, and the normal of (6) is `Fin.snoc β (-μ)` $= (\beta_1, \ldots, \beta_{n-1}, -\mu)$. The minimum $\mu$ is passed as a number together with the two hypotheses that it is attained on $S'$ and is a lower bound on $S'$. The hypothesis $m \ge 1$ ($n \ge 2$, so that $\mathbb{R}^{n-1}$ is a genuine space) is made explicit; for $m = 0$ the statement would be vacuous.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 293, §2 a), (5) and (6) ("Die Ungleichung (6) ist dann eine Stütze an S; und zwar eine extreme Stütze")

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_Representable
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Shared_IsExtremeSupport

namespace WeylPolyhedra.Pyramid

/-- Weyl (1935), §2 a), p. 293 (the induction step of case a)), in the coordinates the paper
chooses there: `n = m + 1 ≥ 2`, and `xₙ ≥ 0` (the normal `Pi.single (Fin.last m) 1`) is an
extreme support of the finite non-degenerate system `S ⊆ ℝⁿ`. `S₀` is the set of points of `S`
with `xₙ = 0`, viewed in `ℝ^(n-1)` by dropping the last coordinate (`Fin.init`), and `S'` is the
set of the other points of `S`. Let `β` be any extreme support of `S₀` in `ℝ^(n-1)` (inequality
(5)) and let `μ` be the minimum of `(β₁x₁ + ⋯ + β_{n-1}x_{n-1}) / xₙ` over the points `x` of
`S'`, attained at some `a ∈ S'`. Then the inequality (6)
`β₁x₁ + ⋯ + β_{n-1}x_{n-1} - μ xₙ ≥ 0`, i.e. the normal `(β₁, …, β_{n-1}, -μ)`, is an extreme
support of `S`. -/
theorem lift_extreme_support {m : ℕ} (hm : 1 ≤ m) (S : Finset (Fin (m + 1) → ℝ))
    (hS : Shared.NonDegenerate S)
    (hlast : Shared.IsExtremeSupport S (Pi.single (Fin.last m) 1))
    (β : Fin m → ℝ)
    (hβ : Shared.IsExtremeSupport ((S.filter (fun x => x (Fin.last m) = 0)).image Fin.init) β)
    (μ : ℝ)
    (hμ_attained : ∃ a ∈ S.filter (fun x => x (Fin.last m) ≠ 0),
      μ = (β ⬝ᵥ Fin.init a) / a (Fin.last m))
    (hμ_min : ∀ x ∈ S.filter (fun x => x (Fin.last m) ≠ 0),
      μ ≤ (β ⬝ᵥ Fin.init x) / x (Fin.last m)) :
    Shared.IsExtremeSupport S (Fin.snoc β (-μ) : Fin (m + 1) → ℝ) := by sorry

end WeylPolyhedra.Pyramid
