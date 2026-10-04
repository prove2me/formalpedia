-- Prove2me | Theorems.Thm_RegretBandits_Linear_bregman_projection_pythagorean
-- name    : RegretBandits.Linear.bregman_projection_pythagorean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:15:03.256415+00:00
-- url     : https://prove2.me/theorems/a715efa8-5767-44dd-8c85-5db30f4ac398
-- title:
--   Lemma 5.2 — generalized Pythagorean inequality for Bregman projections
-- statement:
--   Let $F$ be a Legendre function on $\bar D$, and let $K\subseteq\bar D$ be a closed convex set with $K\cap D\neq\emptyset$. Then for every $x\in D$ the Bregman projection
--   $$z=\arg\min_{y\in K}D_F(y,x)$$
--   exists, is unique and lies in $K\cap D$, and for every $y\in K$
--   $$D_F(y,x)\ \ge\ D_F(y,z)+D_F(z,x).$$
--
--   This is the analogue of the obtuse-angle property of Euclidean projections. In the OMD analysis it controls the effect of the projection step (3).
--
--   **Formalization Note** The book writes "for all $z\in K\cap D$ and $y\in K$". For an arbitrary $z\in K\cap D$ the inequality is false, so it is stated for the projection $z$, which the lemma shows lies in $K\cap D$. The book refers to Cesa-Bianchi and Lugosi (2006, Lemma 11.3) for the proof.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 70–71, Lemma 5.2

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics

namespace RegretBandits.Linear

/-- Lemma 5.2 (Generalized Pythagorean inequality; Bubeck, Cesa-Bianchi, arXiv:1204.5721v2,
pp. 70–71). Let `F` be Legendre on `D̄` and let `K ⊆ D̄` be closed and convex with `K ∩ D ≠ ∅`.
For every `x ∈ D` the Bregman projection `z = argmin_{y ∈ K} D_F(y, x)` exists and is unique, it
lies in `K ∩ D`, and `D_F(y, x) ≥ D_F(y, z) + D_F(z, x)` for all `y ∈ K`. (The book's "for all
`z ∈ K ∩ D`" is read as "for the projection `z`, which lies in `K ∩ D`".) -/
theorem bregman_projection_pythagorean {d : ℕ} {F : (Fin d → ℝ) → ℝ} {D K : Set (Fin d → ℝ)}
    (hF : IsLegendre F D) (hKc : IsClosed K) (hKv : Convex ℝ K) (hKD : K ⊆ closure D)
    (hKne : (K ∩ D).Nonempty) {x : Fin d → ℝ} (hx : x ∈ D) :
    ∃ z, IsBregmanProjection F K x z ∧
      (∀ z', IsBregmanProjection F K x z' → z' = z) ∧
      z ∈ D ∧
      ∀ y ∈ K, bregman F y z + bregman F z x ≤ bregman F y x := by sorry

end RegretBandits.Linear
