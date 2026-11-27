-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_vertex_facet
-- name    : WeylPolyhedra.Polyhedron.Supplement.vertex_facet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T06:38:41.508239+00:00
-- url     : https://prove2.me/theorems/b3397c1d-03d2-4eb0-82df-7422f85573c2
-- title:
--   Satz (§4 I, p. 302) — through every vertex pass $n-1$ independent facets; every facet contains $n-1$ independent vertices
-- statement:
--   Let $S \subseteq \mathbb{R}^m$ be a finite non-degenerate point system of Weyl's inhomogeneous space $\bar R_{n-1} = \mathbb{R}^m$ ($m = n-1$), i.e. its affine span is all of $\mathbb{R}^m$, and let $H$ be its convex hull, the convex polyhedron of $S$. The **facets** of $H$ are the extreme supports $(a, a_0)$ of $S$, i.e. the inequalities $(a x) - a_0 \ge 0$ valid on $S$ with equality at $m$ affinely independent points of $S$. The **vertices** of $H$ are the extreme solutions of the dual system $\Sigma$ normalized to $x_n = -1$: the points $v$ satisfying every facet inequality with equality in $m$ facets that are linearly independent as vectors $(a, a_0) \in \mathbb{R}^m \times \mathbb{R}$. Then:
--
--   1. through every vertex $v$ of $H$ pass at least $n - 1 = m$ independent facets: $m$ facets, linearly independent as vectors $(a, a_0)$, with $(a v) - a_0 = 0$;
--   2. every facet $(a, a_0)$ contains at least $n - 1 = m$ independent vertices: $m$ affinely independent vertices $v$ with $(a v) - a_0 = 0$.
--
--   This is the vertex–facet incidence of a full-dimensional polytope, Satz 12 transferred to the inhomogeneous space.
--
--   (Weyl: "Nennen wir die extremen Stützen von S Seitenflächen, die extremen Lösungen des dualen Systems Σ Ecken von H, so gilt der Satz: Durch jede Ecke des konvexen Polyeders H gehen wenigstens n − 1 unabhängige Seitenflächen hindurch, in jeder Seitenfläche liegen mindestens n − 1 unabhängige Ecken.")
--
--   **Formalization Note** The statement is in the affine form of the published `Polytope` definition: a point $x \in \mathbb{R}^m$ stands for $(x, -1) \in \mathbb{R}^n$, and the homogeneous normal $\alpha$ for $(a, a_0)$. With Weyl's definition of a vertex, clause 1 is close to the definition itself; it is kept, since it is half of the printed theorem. $m$ affinely independent points of $\mathbb{R}^m$ are exactly $m$ points whose homogenizations $(v, -1)$ are linearly independent, Weyl's $n-1$ independent extreme solutions.
--
--   Differences from the source:
--   - encoding: the homogeneous R_n with x_n = −1, and n − 1 independent facets/vertices → affine ℝᵐ (m = n − 1), facets (a, a₀) linearly independent in ℝᵐ × ℝ, vertices affinely independent in ℝᵐ; reason: the base mission's affine form of §4; m linearly independent homogenized points (v, −1) are m affinely independent points v, and (a, a₀) is the homogeneous normal α
--   - encoding: Ecken = extreme solutions of the dual system Σ → IsVertex S v: extreme solutions normalized to x_n = −1; reason: every nonzero point of (Σ) has x_n < 0, since (Σ) is the cone of the points (s, −1) (Satz 6 and Satz 3), so each extreme solution is a positive multiple of exactly one normalized point; Weyl makes the same normalization on p. 303
--   - encoding: wenigstens / mindestens n − 1 → there exist m (= n − 1) such facets / vertices; reason: having m independent ones is having at least m
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 302, §4 I, unnumbered Satz

import Mathlib
import Definitions.Def_WeylPolyhedra_Polyhedron_Polytope
import Definitions.Def_WeylPolyhedra_Polyhedron_Supplement_Vertex

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §4 I, p. 302, the unnumbered Satz, in affine form (`R̄_{n-1} = ℝᵐ`,
`m = n - 1`, a point `x` standing for `(x, -1)`). Let `S ⊆ ℝᵐ` be a finite non-degenerate point
system (affine span the whole space), `H` its convex polyhedron, facets the extreme supports
`(a, a₀)` of `S` and vertices as in `IsVertex`.
1. Through every vertex `v` of `H` pass at least `n - 1 = m` independent facets: `m` facets,
   linearly independent as vectors `(a, a₀) ∈ ℝᵐ × ℝ`, with `a ⬝ᵥ v - a₀ = 0`.
2. Every facet `(a, a₀)` contains at least `n - 1 = m` independent vertices: `m` affinely
   independent vertices `v` (their homogenizations `(v, -1)` linearly independent) with
   `a ⬝ᵥ v - a₀ = 0`. -/
theorem vertex_facet {m : ℕ} (S : Finset (Fin m → ℝ))
    (hS : affineSpan ℝ (S : Set (Fin m → ℝ)) = ⊤) :
    (∀ v : Fin m → ℝ, IsVertex S v →
        ∃ F : Finset ((Fin m → ℝ) × ℝ), F.card = m ∧
          (∀ p ∈ F, IsExtremeAffineSupport S p.1 p.2) ∧
          LinearIndependent ℝ (fun p : F => (p : (Fin m → ℝ) × ℝ)) ∧
          ∀ p ∈ F, p.1 ⬝ᵥ v - p.2 = 0) ∧
      (∀ (a : Fin m → ℝ) (a₀ : ℝ), IsExtremeAffineSupport S a a₀ →
        ∃ V : Finset (Fin m → ℝ), V.card = m ∧
          AffineIndependent ℝ (fun v : V => (v : Fin m → ℝ)) ∧
          ∀ v ∈ V, IsVertex S v ∧ a ⬝ᵥ v - a₀ = 0) := by sorry

end WeylPolyhedra.Polyhedron.Supplement
