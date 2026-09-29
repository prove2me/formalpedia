-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_isConvexPolyhedron_iff
-- name    : WeylPolyhedra.Polyhedron.isConvexPolyhedron_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:08:20.874876+00:00
-- url     : https://prove2.me/theorems/46bbcfa9-1d15-4bac-8dd3-4f80c1cf4704
-- title:
--   §4 II: finitely many inequalities define a convex polyhedron iff their normals positively span and the region has an inner point
-- statement:
--   Let $J$ be a finite index set and consider the inequalities
--   $$A_j \cdot x - b_j \ge 0 \qquad (j \in J)$$
--   on $\mathbb{R}^m$, with normals $A_j \in \mathbb{R}^m$ and constants $b_j \in \mathbb{R}$, no row being identically zero ($A_j \ne 0$ or $b_j \ne 0$). Let $H = \{x : A_j\cdot x - b_j \ge 0 \ \forall j\}$ be the region they cut out. Then $H$ is a convex polyhedron, i.e. $H = \operatorname{conv} S$ for some finite $S \subseteq \mathbb{R}^m$ whose affine span is $\mathbb{R}^m$, if and only if both of the following hold:
--
--   1. every point $\pi' \in \mathbb{R}^m$ is a nonnegative combination of the normals, $\pi' = \sum_{j} \nu_j A_j$ with $\nu_j \ge 0$;
--   2. $H$ has an inner point: there is $c \in \mathbb{R}^m$ with $A_j \cdot c - b_j > 0$ for every $j$.
--
--   This is the half-space description of a full-dimensional polytope (the Minkowski–Weyl theorem for polytopes), with Weyl's explicit criterion for when an intersection of half-spaces is one.
--
--   In Weyl's notation (§4 II, p. 302): the inequalities are $(\alpha x) \equiv \alpha_1 x_1 + \dots + \alpha_{n-1} x_{n-1} - \alpha_n \ge 0$, $(\beta x) \ge 0$, …; condition 1 says that the point system $\Sigma' = \{\alpha', \beta', \dots\}$, $\alpha' = (\alpha_1, \dots, \alpha_{n-1})$, represents every point of $R_{n-1}$ (it has no extreme support), and condition 2 is (15): $(\alpha c) > 0$, $(\beta c) > 0$, …
--
--   **Formalization Note** Weyl's $\bar R_{n-1}$ (the hyperplane $x_n = -1$) is $\mathbb{R}^m$, $m = n-1$, with $A_j = (\alpha_1, \dots, \alpha_{n-1})$ and $b_j = \alpha_n$. "Convex polyhedron" is the hull of a finite **non-degenerate** point system (p. 301), so it is full-dimensional; without this the "only if" would fail (a segment in $\mathbb{R}^2$). The hypothesis that no row is zero is added: Weyl's half-spaces are given by a nonzero point $\alpha$ of the dual space (p. 291), and a zero row $0 \ge 0$ can never hold strictly.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), pp. 302–303, §4 II

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §4 II, pp. 302–303: finitely many inequalities
`(α x) ≡ α₁x₁ + ⋯ + α_{n-1}x_{n-1} - α_n ≥ 0` on `R̄_{n-1} = ℝᵐ` (row `j` has normal
`A j = (α₁, …, α_{n-1})` and constant `b j = α_n`) cut out a region `H`. `H` is a convex
polyhedron (the convex hull of a finite non-degenerate point system) if and only if
(i) every point `π' ∈ ℝᵐ` is a nonnegative linear combination of the normals `A j`, and
(ii) `H` has an inner point: some `c` satisfies every inequality strictly.
Added hypothesis (p. 291: a half-space is given by a nonzero point of the dual space): every
row `(A j, b j)` is nonzero. -/
theorem isConvexPolyhedron_iff {m : ℕ} {J : Type*} [Fintype J] (A : J → Fin m → ℝ)
    (b : J → ℝ) (hrow : ∀ j, A j ≠ 0 ∨ b j ≠ 0) :
    IsConvexPolyhedron (inequalityRegion A b) ↔
      ((∀ π' : Fin m → ℝ, ∃ ν : J → ℝ, (∀ j, 0 ≤ ν j) ∧ π' = ∑ j, ν j • A j) ∧
        ∃ c : Fin m → ℝ, ∀ j, 0 < A j ⬝ᵥ c - b j) := by sorry

end WeylPolyhedra.Polyhedron
