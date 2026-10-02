-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_linear_stable_unstable
-- name    : TeschlODE.LocalBehavior.linear_stable_unstable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:23:06.94205+00:00
-- url     : https://prove2.me/theorems/cf2b7d31-c656-4d2b-ba60-f47fabc32aee
-- title:
--   Theorem 9.2 — linear stable/unstable subspaces are invariant, with exponential rates (9.4)
-- statement:
--   Let $A$ be a real $n \times n$ matrix with eigenvalues $\alpha_j$, and let $E^+ = E^+(e^A)$ and $E^- = E^-(e^A)$ be the real spans of the generalized eigenvectors for eigenvalues with $\operatorname{Re}\alpha_j < 0$ and $\operatorname{Re}\alpha_j > 0$, respectively. Then $E^\pm$ are invariant under the flow $e^{tA}$ for all $t \in \mathbb{R}$, every $x^\pm \in E^\pm$ satisfies $e^{tA} x^\pm \to 0$ as $t \to \pm\infty$, and more precisely
--   $$|e^{tA} x^\pm| \le C e^{\mp t\alpha} |x^\pm|, \qquad \pm t \ge 0, \quad x^\pm \in E^\pm, \qquad (9.4)$$
--   for every $\alpha < \min\{|\operatorname{Re}\alpha_j| : \pm\operatorname{Re}\alpha_j < 0\}$ and some $C > 0$ depending on $\alpha$.
--
--   This is the linear model for everything in the chapter: the stable manifold theorem is its nonlinear counterpart and the Hartman–Grobman theorem shows that near a hyperbolic fixed point the nonlinear flow is a continuous deformation of $e^{tA}$.
--
--   **Formalization Note.** Stated for both signs at once as six conjuncts (two invariances, two limits, two bounds). "Some $C > 0$ depending on $\alpha$" is read as $\forall \alpha,\ \exists C > 0,\ \forall t, \forall x$: $C$ depends on $\alpha$ (and $A$), not on $t$ or $x$. The minimum over an empty set is $+\infty$, so if no eigenvalue has $\pm \operatorname{Re} < 0$ every $\alpha$ is allowed (and $E^\pm = 0$). $|\cdot|$ is the sup norm of `Fin n → ℝ` instead of the book's Euclidean norm; the two differ by a factor at most $\sqrt n$, which the existential $C$ absorbs, so the statement is equivalent. $e^{tA}$ is `NormedSpace.exp (t • A)` in the matrix algebra.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 254, Theorem 9.2

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues
import Definitions.Def_TeschlODE_LocalBehavior_spectralSubspace

namespace TeschlODE.LocalBehavior

/-- Teschl, Theorem 9.2, p. 254: for any real `n × n` matrix `A`, the linear stable and unstable
subspaces `E₊ = E₊(e^A)` (generalized eigenvectors for `Re α_j < 0`) and `E₋ = E₋(e^A)`
(`Re α_j > 0`) are invariant under the flow `e^{tA}`, every point of `E±` converges to `0` as
`t → ±∞`, and (9.4) holds: for every `α` below `min {|Re α_j| : ±Re α_j < 0}` (any `α` if that
set is empty) there is `C > 0`, depending on `α` only, with
`|e^{tA} x₊| ≤ C e^{-tα} |x₊|` for `t ≥ 0`, `x₊ ∈ E₊`, and
`|e^{tA} x₋| ≤ C e^{tα} |x₋|` for `t ≤ 0`, `x₋ ∈ E₋`. -/
theorem linear_stable_unstable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (t : ℝ), ∀ x ∈ spectralSubspace A {z | z.re < 0},
      (NormedSpace.exp (t • A)).mulVec x ∈ spectralSubspace A {z | z.re < 0}) ∧
    (∀ (t : ℝ), ∀ x ∈ spectralSubspace A {z | 0 < z.re},
      (NormedSpace.exp (t • A)).mulVec x ∈ spectralSubspace A {z | 0 < z.re}) ∧
    (∀ x ∈ spectralSubspace A {z | z.re < 0},
      Filter.Tendsto (fun t : ℝ => (NormedSpace.exp (t • A)).mulVec x) Filter.atTop (nhds 0)) ∧
    (∀ x ∈ spectralSubspace A {z | 0 < z.re},
      Filter.Tendsto (fun t : ℝ => (NormedSpace.exp (t • A)).mulVec x) Filter.atBot (nhds 0)) ∧
    (∀ α : ℝ, (∀ z ∈ eigenvalues A, z.re < 0 → α < |z.re|) →
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x ∈ spectralSubspace A {z | z.re < 0},
        ‖(NormedSpace.exp (t • A)).mulVec x‖ ≤ C * Real.exp (-t * α) * ‖x‖) ∧
    (∀ α : ℝ, (∀ z ∈ eigenvalues A, 0 < z.re → α < |z.re|) →
      ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t ≤ 0 → ∀ x ∈ spectralSubspace A {z | 0 < z.re},
        ‖(NormedSpace.exp (t • A)).mulVec x‖ ≤ C * Real.exp (t * α) * ‖x‖) := by sorry

end TeschlODE.LocalBehavior
