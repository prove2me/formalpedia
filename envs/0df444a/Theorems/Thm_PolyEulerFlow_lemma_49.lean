-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_49
-- name    : PolyEulerFlow.lemma_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:20.357666+00:00
-- url     : https://prove2.me/theorems/8d56b191-9b08-4da2-9f93-9bcd88dc8e57
-- title:
--   Lemma 49 — uniform Euler-to-ODE limit
-- statement:
--   Let $f$ be a locally Lipschitz field on $\mathbb R^N$ (for instance $F(x,h,\cdot)$ at a fixed input and scale) and $z_0\in\mathbb R^N$. Suppose the exact Euler orbits $z^{(\eta)}_{k+1}=z^{(\eta)}_k+\eta f(z^{(\eta)}_k)$, $z^{(\eta)}_0=z_0$, stay in a common box $[lo,hi]$ for every $0<\eta\le1$. Then:
--
--   1. the equation $\dot z=f(z)$, $z(0)=z_0$ has a global solution on $[0,\infty)$, and it is unique;
--   2. the piecewise-affine interpolants of the Euler orbits converge to it uniformly on every interval $[0,T]$ as $\eta\to0^+$;
--   3. if $M$ and $A\ge1$ bound $\|f\|$ and the Lipschitz constant of $f$ on a convex compact neighborhood $U$ of the box, then for every $T\ge0$ the interpolation error on $[0,T]$ is at most $AM\eta Te^{AT}$ once $\eta$ is small enough.
--
--   Differences from the source:
--   - generalization: the polynomial field F(x, h, ·) at a fixed input and scale → any locally Lipschitz field on ℝ^N; reason: every polynomial field is locally Lipschitz
--   - reading: the unique global solution → a continuous solution of the integral equation on [0, ∞), which exists and equals every other such solution; reason: for a continuous field this is the C¹ solution
--   - reading: converge on every bounded physical interval → uniform convergence on [0, T] for every T ≥ 0, along η → 0⁺; reason: 'converge' for interpolants on an interval with a uniform error bound
--   - reading: a convex compact neighborhood of the box → a convex compact U whose interior contains [lo, hi]; reason: definition of a neighborhood of a set
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 49, p.37 (PDF 39)

import Mathlib
import Definitions.Def_PolyEulerFlow_IsForcedSolution

open Filter Topology

namespace PolyEulerFlow

/-- **Lemma 49 (Uniform Euler-to-ODE limit)**, p.37 (PDF 39). Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript,
sha256 c4e01b2b…).

Fix an input and an allowed scale, so that the field `f = F(x, h, ·)` and the initial state `c(x, h)` are fixed. Suppose the exact Euler orbits, for every
`0 < η ≤ 1`, stay in a common compact box. Then the global solution of `ż = f(z)`, `z(0) = c(x, h)` exists and is unique, and the piecewise-affine
interpolants converge to it uniformly on every bounded physical interval `[0, T]` as `η → 0`. If `M` and `A ≥ 1` bound the field and its Lipschitz
constant on a convex compact neighborhood of the box, the interpolation error up to time `T` is at most `AMηTe^{AT}` once `η` is small enough.

**Formalization Note** The field is any locally Lipschitz map of `ℝ^N` (every polynomial field is one). The solution is a continuous solution of the
integral equation on `[0, ∞)` (`IsForcedSolution` with zero forcing), unique among those. The box is `[lo, hi]`; a neighborhood `U` of it is a set
whose interior contains it. -/
theorem lemma_49 {N : ℕ} (f : (Fin N → ℝ) → Fin N → ℝ) (hf : LocallyLipschitz f) (z0 lo hi : Fin N → ℝ)
    (hbox : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ k, eulerOrbit f z0 (fun _ => η) (fun _ => 0) k ∈ Set.Icc lo hi) :
    ∃ z : ℝ → Fin N → ℝ, IsForcedSolution f z0 (fun _ => 0) z ∧
      (∀ w : ℝ → Fin N → ℝ, IsForcedSolution f z0 (fun _ => 0) w → ∀ t, 0 ≤ t → w t = z t) ∧
      (∀ T : ℝ, 0 ≤ T →
        TendstoUniformlyOn (fun (η : ℝ) (t : ℝ) => eulerInterpolant (eulerOrbit f z0 (fun _ => η) (fun _ => 0)) η t)
          z (𝓝[>] 0) (Set.Icc 0 T)) ∧
      (∀ (U : Set (Fin N → ℝ)) (Mb : ℝ) (A : NNReal), Convex ℝ U → IsCompact U → Set.Icc lo hi ⊆ interior U →
        1 ≤ A → (∀ y ∈ U, ‖f y‖ ≤ Mb) → LipschitzOnWith A f U →
        ∀ T : ℝ, 0 ≤ T → ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η ≤ η0 → ∀ t ∈ Set.Icc 0 T,
          ‖eulerInterpolant (eulerOrbit f z0 (fun _ => η) (fun _ => 0)) η t - z t‖
            ≤ (A : ℝ) * Mb * η * T * Real.exp ((A : ℝ) * T)) := by sorry

end PolyEulerFlow
