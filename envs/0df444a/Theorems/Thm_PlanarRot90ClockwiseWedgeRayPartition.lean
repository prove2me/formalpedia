-- Prove2me | Theorems.Thm_PlanarRot90ClockwiseWedgeRayPartition
-- name    : PlanarRot90ClockwiseWedgeRayPartition
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T20:25:58.584157+00:00
-- url     : https://prove2.me/theorems/1a18b8ea-44d7-4495-a227-6598a3124f87
-- title:
--   Planar Rot90 Clockwise Wedge Ray Partition
-- statement:
--   Let $\iota$ be a nonempty finite set of nonzero rays based at a point
--   $p\in\mathbb R^2$, represented by vectors $u_i$, and let
--   $\rho>0$.  Assume distinct indices determine distinct positive rays.
--   Assume also that each $u_i$ is a positive multiple of the unit vector with
--   normalized angle $\theta_i\in[0,2\pi)$, that the angles $\theta_i$ are
--   injective, and that a permutation $\operatorname{next}$ and turn function
--   $T(i,j)$ have the following finite cyclic-order properties:
--   $$
--     T(i,j)=
--     \begin{cases}
--       2\pi, & j=i,\\
--       \theta_i-\theta_j, & j\ne i\text{ and }\theta_j<\theta_i,\\
--       \theta_i-\theta_j+2\pi, & j\ne i\text{ and }\theta_i<\theta_j,
--     \end{cases}
--   $$
--   $\operatorname{next}(i)=i$ if and only if $i$ is the only index, every
--   open clockwise interval from $i$ to $\operatorname{next}(i)$ contains no
--   listed angle, and every normalized angle not among the listed angles lies in
--   one of those open intervals.  Concretely, for
--   $\alpha\in[0,2\pi)$, write
--   $$
--     \tau_i(\alpha)=
--     \begin{cases}
--       2\pi, & \alpha=\theta_i,\\
--       \theta_i-\alpha, & \alpha<\theta_i,\\
--       \theta_i-\alpha+2\pi, & \theta_i<\alpha.
--     \end{cases}
--   $$
--   The interval assumptions mean that
--   $$
--     0<\tau_i(\alpha)<T(i,\operatorname{next}(i))
--   $$
--   forces $\alpha\ne\theta_j$ for every $j$, and that every
--   $\alpha\in[0,2\pi)$ not equal to any $\theta_j$ satisfies this strict
--   double inequality for at least one $i$.
--
--   Then there are sectors $\Sigma_i\subset\mathbb R^2$ with the following
--   properties.  If $\operatorname{next}(i)=i$, then
--   $$
--     \Sigma_i
--     =B(p,\rho)\setminus
--       \bigl(\{p+t u_i:t>0\}\cup\{p\}\bigr).
--   $$
--   If $\operatorname{next}(i)\ne i$, then there are real numbers $c_i,s_i$,
--   with $s_i\ne0$ or $c_i<0$, such that
--   $$
--     u_{\operatorname{next}(i)}
--      =c_i u_i-s_i\operatorname{rot}_{90}(u_i).
--   $$
--   Writing
--   $$
--     \Phi_i(x,y)=p+xu_i+y\operatorname{rot}_{90}(u_i),
--   $$
--   the sector is
--   $$
--    \begin{cases}
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\ y<0,\
--      c_i y+s_i x>0\}, & s_i>0,\\
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\
--      (y<0\text{ or }c_i y+s_i x>0)\}, & s_i<0,\\
--    \Phi_i\{(x,y):x^2+y^2<(\rho/\|u_i\|)^2,\ y<0\}, & s_i=0.
--    \end{cases}
--   $$
--   Every $\Sigma_i$ is open and connected, lies in $B(p,\rho)$, and is
--   disjoint from every positive ray $\{p+t u_j:t>0\}$.  Finally, every point
--   of $B(p,\rho)\setminus\{p\}$ that lies on none of the positive rays belongs
--   to at least one $\Sigma_i$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PlanarRot90ClockwiseWedgeRayPartition`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90ClockwiseWedgeRayPartition.lean#L1-L595

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90ClockwiseWedgeRayPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (p : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ)
    (u : ι → EuclideanSpace ℝ (Fin 2))
    (θ : ι → ℝ)
    (clockwiseNext : Equiv.Perm ι)
    (clockwiseTurn : ι → ι → ℝ)
    (hρ : 0 < ρ)
    (hu : ∀ i : ι, u i ≠ 0)
    (hposRayDistinct :
      ∀ {i j : ι}, (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j)
    (hθ_mem : ∀ i : ι, 0 ≤ θ i ∧ θ i < 2 * Real.pi)
    (hθ_inj : Function.Injective θ)
    (hθ_ray :
      ∀ i : ι, ∃ r : ℝ, 0 < r ∧
        u i =
          r • WithLp.toLp 2
            (fun k : Fin 2 =>
              if k = 0 then Real.cos (θ i) else Real.sin (θ i)))
    (hturn_eq : ∀ i j : ι,
      clockwiseTurn i j =
        if j = i then 2 * Real.pi
        else if θ j < θ i then θ i - θ j
        else θ i - θ j + 2 * Real.pi)
    (hfixed_singleton :
      ∀ i : ι, clockwiseNext i = i ↔ ∀ j : ι, j = i)
    (hangleGapEmpty :
      ∀ i : ι, ∀ α : ℝ,
        0 ≤ α → α < 2 * Real.pi →
          0 <
            (if α = θ i then 2 * Real.pi
             else if α < θ i then θ i - α
             else θ i - α + 2 * Real.pi) →
          (if α = θ i then 2 * Real.pi
           else if α < θ i then θ i - α
           else θ i - α + 2 * Real.pi) <
            clockwiseTurn i (clockwiseNext i) →
          ∀ j : ι, θ j ≠ α)
    (hangleGapCover :
      ∀ α : ℝ,
        0 ≤ α → α < 2 * Real.pi →
          (∀ j : ι, θ j ≠ α) →
            ∃ i : ι,
              0 <
                (if α = θ i then 2 * Real.pi
                 else if α < θ i then θ i - α
                 else θ i - α + 2 * Real.pi) ∧
              (if α = θ i then 2 * Real.pi
               else if α < θ i then θ i - α
               else θ i - α + 2 * Real.pi) <
                clockwiseTurn i (clockwiseNext i)) :
    ∃ sector : ι → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i : ι,
        if h : clockwiseNext i = i then
          sector i =
            Metric.ball p ρ \
              ({q | ∃ t : ℝ, 0 < t ∧ q = p + t • u i} ∪
                ({p} : Set (EuclideanSpace ℝ (Fin 2))))
        else
          ∃ c s : ℝ,
            (s ≠ 0 ∨ c < 0) ∧
            u (clockwiseNext i) = c • u i - s • PlanarRot90 (u i) ∧
            sector i =
              (let base : EuclideanSpace ℝ (Fin 2) := u i
               let baseChart : EuclideanSpace ℝ (Fin 2) →
                  EuclideanSpace ℝ (Fin 2) :=
                fun z => p + z 0 • base + z 1 • PlanarRot90 base
               if 0 < s then
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
               else if s < 0 then
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
               else
                 baseChart ''
                  {z : EuclideanSpace ℝ (Fin 2) |
                    z 0 ^ 2 + z 1 ^ 2 < (ρ / ‖base‖) ^ 2 ∧
                    z 1 < 0})) ∧
      (∀ i : ι, IsOpen (sector i) ∧ IsConnected (sector i)) ∧
      (∀ i : ι, sector i ⊆ Metric.ball p ρ) ∧
      (∀ i j : ι,
        Disjoint (sector i)
          {q | ∃ t : ℝ, 0 < t ∧ q = p + t • u j}) ∧
      (∀ q : EuclideanSpace ℝ (Fin 2),
        q ∈ Metric.ball p ρ →
          q ≠ p →
            (∀ i : ι,
              q ∉ {x | ∃ t : ℝ, 0 < t ∧ x = p + t • u i}) →
              ∃ i : ι, q ∈ sector i) := by sorry
