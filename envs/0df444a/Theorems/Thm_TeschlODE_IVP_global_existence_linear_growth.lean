-- Prove2me | Theorems.Thm_TeschlODE_IVP_global_existence_linear_growth
-- name    : TeschlODE.IVP.global_existence_linear_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:52:44.496632+00:00
-- url     : https://prove2.me/theorems/659c6e01-0782-4419-8dd7-fc1deb42b820
-- title:
--   Theorem 2.17 — solutions exist for all t ∈ ℝ under the linear growth bound (2.66)
-- statement:
--   Let $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$ be continuous (the book's case $U = \mathbb{R} \times \mathbb{R}^n$), and suppose that for every $T > 0$ there are constants $M(T)$, $L(T)$ with
--   $$|f(t, x)| \le M(T) + L(T)|x|, \qquad (t, x) \in [-T, T] \times \mathbb{R}^n. \qquad (2.66)$$
--   Then all solutions of the IVP (2.10) are defined for all $t \in \mathbb{R}$: if $I$ is an open interval containing $t_0$ and $\varphi$ solves $\dot x = f(t,x)$ on $I$ with $\varphi(t_0) = x_0$, then there is a solution $\psi$ of $\dot x = f(t,x)$ on all of $\mathbb{R}$ that agrees with $\varphi$ on $I$.
--
--   The constants may depend on $T$ but not on $x$. Problem 2.18 of the book shows the conclusion fails for superlinear growth $|x|^\alpha$, $\alpha > 1$.
--
--   **Formalization Note.** "All solutions are defined for all $t \in \mathbb{R}$" is read as: every solution on an open interval extends to a global solution; equivalently, every maximal solution is global. Open intervals, including unbounded ones, are the sets that are open and order-connected. The statement assumes only continuity of $f$, as Theorem 2.17's own text does; §2.6 opens with a standing assumption of local uniqueness (e.g. $f$ Lipschitz), but the book's remark on p. 51 extends maximal solutions to the case without uniqueness, and the conclusion as stated holds for every continuous $f$ satisfying (2.66). The constants $M(T), L(T)$ are real numbers with no sign constraint (the bound forces $M(T) \ge 0$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 53, Theorem 2.17

import Mathlib
import Definitions.Def_TeschlODE_IVP_IsSolutionOn

namespace TeschlODE.IVP

theorem global_existence_linear_growth {n : ℕ}
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : Continuous f)
    (hgrowth : ∀ T : ℝ, 0 < T → ∃ M L : ℝ, ∀ t ∈ Set.Icc (-T) T,
      ∀ x : EuclideanSpace ℝ (Fin n), ‖f (t, x)‖ ≤ M + L * ‖x‖)
    (t₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (ht₀ : t₀ ∈ I)
    (φ : ℝ → EuclideanSpace ℝ (Fin n)) (hφ : IsSolutionOn Set.univ f I φ) (hφ₀ : φ t₀ = x₀) :
    ∃ ψ : ℝ → EuclideanSpace ℝ (Fin n), IsSolutionOn Set.univ f Set.univ ψ ∧
      Set.EqOn ψ φ I := by sorry

end TeschlODE.IVP
