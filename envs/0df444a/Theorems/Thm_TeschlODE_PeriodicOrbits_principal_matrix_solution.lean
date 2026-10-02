-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_principal_matrix_solution
-- name    : TeschlODE.PeriodicOrbits.principal_matrix_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:55:56.372386+00:00
-- url     : https://prove2.me/theorems/b1dfe01b-563b-461c-a35d-c3cd97f86527
-- title:
--   Lemma 12.1 — the principal matrix solution of the first variational equation is $\partial\Phi_{t-t_0}/\partial x$; $f(\Phi(t,x_0))$ solves it
-- statement:
--   Throughout, $f \in C^k(M, \mathbb{R}^n)$ with $k \ge 1$ on an open set $M \subseteq \mathbb{R}^n$, $\Phi$ is its flow with maximal intervals $I_x$, and $x_0 \in M$ is a periodic point of period $T = T(x_0) > 0$ (standing assumptions of Chapter 6 and §12.1). Let $A(t) = df_{\Phi(t, x_0)}$ (12.3) and consider the **first variational equation** $\dot y = A(t) y$ (12.4).
--
--   Then the principal matrix solution of (12.4) is
--   $$\Pi_{x_0}(t, t_0) = \frac{\partial \Phi_{t - t_0}}{\partial x}\big(\Phi(t_0, x_0)\big), \qquad (12.5)$$
--   that is, $J(t, t_0) := \frac{\partial \Phi_{t-t_0}}{\partial x}(\Phi(t_0, x_0))$ exists, $J(t_0, t_0) = \mathbb{I}$ and $\frac{\partial}{\partial t} J(t, t_0) = A(t) J(t, t_0)$ for all $t, t_0$; moreover $f(\Phi(t, x_0))$ is a solution of (12.4):
--   $$f(\Phi(t, x_0)) = \Pi_{x_0}(t, t_0)\, f(\Phi(t_0, x_0)). \qquad (12.6)$$
--
--   The lemma identifies the linearization of the flow along the periodic orbit with the Floquet theory of §3.6 for the periodic matrix $A(t)$, and it is where the eigenvalue $1$ of the monodromy matrix (12.8) comes from.
--
--   **Formalization Note.** The principal matrix solution is by definition the unique solution of $\dot \Pi = A(t)\Pi$, $\Pi(t_0, t_0) = \mathbb{I}$; the statement asserts that $J$ satisfies exactly this initial value problem (in the space of continuous linear maps), which by uniqueness is (12.5). The derivative is `fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀)`; its existence is asserted as a separate conjunct so no junk value can satisfy the statement.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 316, Lemma 12.1, Eqs. (12.5)–(12.6)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Lemma 12.1, p. 316. Let `f ∈ Cᵏ(M, ℝⁿ)`, `k ≥ 1`, `M` open, with flow `Φ`, and let
`Φ(t, x₀)` be a periodic solution of period `T = T(x₀) > 0` (standing assumption of §12.1). Put
`A(t) = df_{Φ(t, x₀)}` (12.3). Then `J(t, t₀) = ∂Φ_{t−t₀}/∂x (Φ(t₀, x₀))` is the principal matrix
solution of the first variational equation `ẏ = A(t) y` (12.4), i.e. (12.5): `J(t₀, t₀) = I` and
`∂_t J(t, t₀) = A(t) J(t, t₀)` (with `∂Φ_{t−t₀}/∂x` existing at `Φ(t₀, x₀)`); and (12.6):
`f(Φ(t, x₀)) = J(t, t₀) f(Φ(t₀, x₀))`. The principal matrix solution is by definition the
unique solution of this matrix initial value problem, so the first two clauses say exactly
`Π_{x₀}(t, t₀) = J(t, t₀)`. -/
theorem principal_matrix_solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ))
    (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f M)
    (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : TeschlODE.Shared.IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : IsRegularPeriodicPoint I Φ x₀ T) :
    (∀ t₀ : ℝ, fderiv ℝ (Φ (t₀ - t₀)) (Φ t₀ x₀) = ContinuousLinearMap.id ℝ (Fin n → ℝ)) ∧
    ∀ t₀ t : ℝ,
      DifferentiableAt ℝ (Φ (t - t₀)) (Φ t₀ x₀) ∧
      HasDerivAt (fun s : ℝ => fderiv ℝ (Φ (s - t₀)) (Φ t₀ x₀))
        ((fderiv ℝ f (Φ t x₀)).comp (fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀))) t ∧
      f (Φ t x₀) = fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀) (f (Φ t₀ x₀)) := by sorry

end TeschlODE.PeriodicOrbits
