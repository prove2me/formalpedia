-- Prove2me | Theorems.Thm_TeschlODE_PeriodicOrbits_hyperbolic_periodic_orbit_persists
-- name    : TeschlODE.PeriodicOrbits.hyperbolic_periodic_orbit_persists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:25:03.233575+00:00
-- url     : https://prove2.me/theorems/35413c00-4878-422b-9dee-f7fa6bf1e567
-- title:
--   Lemma 12.7 — hyperbolic periodic orbits persist under small $C^k$ perturbations
-- statement:
--   Let $M \subseteq \mathbb{R}^n$ and $\Lambda \subseteq \mathbb{R}^p$ be open with $0 \in \Lambda$, let $f(x, \mu)$ be $C^k$ ($k \ge 1$) on $M \times \Lambda$, and for each $\mu \in \Lambda$ let $\Phi^\mu$ be the flow of $\dot x = f(x, \mu)$ with maximal intervals $I^\mu_x$. Suppose $f(x, 0)$ has a hyperbolic periodic orbit $\gamma(x_0)$ of period $T$. Then there are an open neighborhood $W \subseteq \Lambda$ of $0$ and a $C^k$ map $\mu \mapsto x_0(\mu)$ on $W$ with
--   $$x_0(0) = x_0, \qquad \gamma(x_0(\mu)) \text{ is a periodic orbit of } f(x, \mu) \quad (\mu \in W),$$
--   i.e. each $x_0(\mu)$ is a periodic point of $\Phi^\mu$ with some positive period $T(\mu)$.
--
--   This is the persistence of hyperbolic periodic orbits: a periodic orbit whose Poincaré map has no multiplier on the unit circle survives every small smooth perturbation of the vector field, and depends smoothly on the perturbation.
--
--   **Formalization Note.** The book writes the parameter as $\lambda$ (a reserved word in Lean), here $\mu \in \mathbb{R}^p$; it does not specify the parameter space, and a finite-dimensional one is taken. "In a sufficiently small neighborhood of $0$" is read as $\exists\, W$ open with $0 \in W \subseteq \Lambda$. "Periodic orbit" means a regular one (positive period), so a family of fixed points does not qualify. Hyperbolicity is `IsHyperbolicPeriodicPoint` (no eigenvalue of $dP_\Sigma(x_0)$ on the unit circle), the notion the book's proof uses.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 319, Lemma 12.7

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow
import Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
import Definitions.Def_TeschlODE_PeriodicOrbits_IsHyperbolicPeriodicPoint

namespace TeschlODE.PeriodicOrbits

/-- Teschl, Lemma 12.7, p. 319. Let `f(x, μ)` be `Cᵏ`, `k ≥ 1`, on `M × Λ` (`M ⊆ ℝⁿ`, `Λ ⊆ ℝᵖ`
open, `0 ∈ Λ`), with flows `Φ^μ` of `ẋ = f(x, μ)` for `μ ∈ Λ`, and suppose `f(x, 0)` has a
hyperbolic periodic orbit `γ(x₀)` of period `T`. Then, in a sufficiently small neighborhood of
`0` there is a `Cᵏ` map `μ ↦ x₀(μ)` with `x₀(0) = x₀` such that `γ(x₀(μ))` is a periodic orbit
of `f(x, μ)`. The book's "in a sufficiently small neighborhood of 0" is read as: there is an
open `W ∋ 0`, `W ⊆ Λ`, on which `x₀(·)` is `Cᵏ` and each `x₀(μ)` is a regular periodic point
(positive period) of `Φ^μ`. The book writes the parameter as `λ`. -/
theorem hyperbolic_periodic_orbit_persists {n p : ℕ}
    (f : (Fin n → ℝ) × (Fin p → ℝ) → (Fin n → ℝ)) (M : Set (Fin n → ℝ)) (Λ : Set (Fin p → ℝ))
    (hM : IsOpen M) (hΛ : IsOpen Λ) (hΛ0 : (0 : Fin p → ℝ) ∈ Λ)
    (k : ℕ) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f (M ×ˢ Λ))
    (I : (Fin p → ℝ) → (Fin n → ℝ) → Set ℝ) (Φ : (Fin p → ℝ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hΦ : ∀ μ ∈ Λ, TeschlODE.Shared.IsMaximalFlow (fun x => f (x, μ)) M (I μ) (Φ μ))
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ)
    (hhyp : IsHyperbolicPeriodicPoint (fun x => f (x, 0)) M k (I 0) (Φ 0) x₀ T) :
    ∃ W : Set (Fin p → ℝ), IsOpen W ∧ (0 : Fin p → ℝ) ∈ W ∧ W ⊆ Λ ∧
      ∃ x₀' : (Fin p → ℝ) → (Fin n → ℝ), ContDiffOn ℝ k x₀' W ∧ x₀' 0 = x₀ ∧
        ∀ μ ∈ W, x₀' μ ∈ M ∧ ∃ T' : ℝ, IsRegularPeriodicPoint (I μ) (Φ μ) (x₀' μ) T' := by sorry

end TeschlODE.PeriodicOrbits
