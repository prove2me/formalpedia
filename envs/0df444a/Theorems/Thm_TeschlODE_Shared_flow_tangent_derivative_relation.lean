-- Prove2me | Theorems.Thm_TeschlODE_Shared_flow_tangent_derivative_relation
-- name    : TeschlODE.Shared.flow_tangent_derivative_relation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-04T15:45:54.926133+00:00
-- url     : https://prove2.me/theorems/b1859bba-f830-4418-a99a-30ffc94f6d4b
-- title:
--   The vector field along a periodic orbit solves the first variational equation (12.6)
-- statement:
--   **Eq. (12.6): the tangent direction solves the variational equation.** Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1`, `Φ` the flow of `ẋ = f(x)`, and `x₀ ∈ M` a periodic point of period `T > 0`. Then for all `t₀, t : ℝ`,
--
--   ```
--   f (Φ t x₀) = ∂Φ_(t - t₀)/∂x (Φ t₀ x₀) (f (Φ t₀ x₀))
--   ```
--
--   **Proof (Teschl, p. 316).** Differentiate the flow property (6.11), `Φ(t, x₀) = Φ(t - t₀, Φ t₀ x₀)`, with respect to `t₀`. The left-hand side is constant, so
--
--   ```
--   0 = ∂Φ(t - t₀, Φ t₀ x₀)/∂t₀ = -f(Φ(t - t₀, Φ t₀ x₀)) + Π_{x₀}(t, t₀) f(Φ t₀ x₀)
--   ```
--
--   where the first summand is the chain rule through `s ↦ s ↦ Φ s y` (that is, `f` applied to the current position) and the second is the chain rule through `y ↦ Φ(t - t₀) y`. Using (6.11) again, `Φ(t - t₀, Φ t₀ x₀) = Φ(t, x₀)`, and rearranging gives the identity.
--
--   **Why the eigenvalue 1 exists.** Applying (12.6) at `t = t₀` gives the zero-time-shift Jacobian (12.5) applied to `f (Φ t₀ x₀)`, i.e. `f (Φ t₀ x₀) = f (Φ t₀ x₀)`. At `t = t₀ + T` periodicity turns it into `M_{x₀}(t₀) f(Φ t₀ x₀) = f(Φ t₀ x₀)`, which is Eq. (12.8). So `M_{x₀}(t₀)` has eigenvalue `1` with eigenvector `f(Φ t₀ x₀)`. This is the fact that makes the characteristic-polynomial identity `charpoly M = (X - 1) * charpoly dP_Σ` of Theorem 12.4 come out with exactly one factor of `(X - 1)`: the complementary invariant subspace is `T_{x₀}Σ = ker (∂S/∂x)(x₀)`, which `f(Φ x₀)` is transverse to by the transversality hypothesis `fderiv ℝ S x₀ (f x₀) ≠ 0`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 316, §12.1 Eq. (12.6) and Eq. (12.8)

import Mathlib
import Definitions.Def_TeschlODE_Shared_IsMaximalFlow

namespace TeschlODE.Shared

/-- Teschl, §12.1, p. 316, Eq. (12.6): `f (Φ(t, x₀))` solves the first variational equation.

Let `f ∈ C^k(M, ℝⁿ)` with `k ≥ 1`, `Φ` the flow of `ẋ = f(x)` with maximal intervals `I`, and
`x₀ ∈ M` a periodic point of period `T > 0`. Then for all `t₀, t : ℝ`,

`f (Φ t x₀) = (∂Φ_(t - t₀)/∂x (Φ t₀ x₀)) (f (Φ t₀ x₀))`.

This is Eq. (12.6): the vector field along the orbit is a solution of `ẏ = A(t) y`. It is the
precise source of the eigenvalue `1` of the monodromy matrix, since (12.8) reads
`M_{x₀}(t₀) f (Φ t₀ x₀) = f (Φ t₀ x₀)`.

Teschl's proof differentiates the flow property (6.11), `Φ(t, x₀) = Φ(t - t₀, Φ t₀ x₀)`, with
respect to `t₀`:

`0 = ∂Φ(t, x₀)/∂t₀ = ∂Φ(t - t₀, Φ t₀ x₀)/∂t₀ = -f(Φ(t - t₀, Φ t₀ x₀)) + Π_{x₀}(t, t₀) f(Φ t₀ x₀)`,

using the flow property again to identify `Φ(t - t₀, Φ t₀ x₀) = Φ(t, x₀)`. Rearranging gives (12.6). -/
theorem flow_tangent_derivative_relation {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (M : Set (Fin n → ℝ)) (hM : IsOpen M) (k : ℕ) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f M) (I : (Fin n → ℝ) → Set ℝ)
    (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ M) (T : ℝ) (hper : 0 < T ∧ T ∈ I x₀ ∧ Φ T x₀ = x₀)
    (t₀ t : ℝ) :
    f (Φ t x₀) = fderiv ℝ (Φ (t - t₀)) (Φ t₀ x₀) (f (Φ t₀ x₀)) := by sorry

end TeschlODE.Shared
