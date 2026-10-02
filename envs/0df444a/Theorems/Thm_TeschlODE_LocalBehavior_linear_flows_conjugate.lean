-- Prove2me | Theorems.Thm_TeschlODE_LocalBehavior_linear_flows_conjugate
-- name    : TeschlODE.LocalBehavior.linear_flows_conjugate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:48:08.804645+00:00
-- url     : https://prove2.me/theorems/73eabc93-cbdb-406b-80a7-499be109f98a
-- title:
--   Theorem 9.10 — hyperbolic linear flows with equal stable/unstable dimensions are topologically conjugate
-- statement:
--   Let $A$ and $B$ be real $n \times n$ matrices with no eigenvalues on the imaginary axis. Suppose the stable subspaces $E^+(e^A)$, $E^+(e^B)$ (generalized eigenvectors for eigenvalues with negative real part) have the same dimension, and the unstable subspaces $E^-(e^A)$, $E^-(e^B)$ (positive real part) have the same dimension. Then the flows are **topologically conjugate** (9.39): there is a homeomorphism $\phi$ of $\mathbb{R}^n$ with
--   $$\phi \circ e^{tA} = e^{tB} \circ \phi \qquad \text{for all } t \in \mathbb{R}.$$
--
--   Combined with the Hartman–Grobman theorem, this classifies $C^1$ vector fields near hyperbolic fixed points up to local topological conjugacy by the two dimensions alone.
--
--   **Formalization Note.** The dimensions are `Module.finrank ℝ` of the real spectral subspaces. The conjugacy is global (on all of $\mathbb{R}^n$ and for all $t \in \mathbb{R}$), as in the book; $\phi$ is not required to be of the form identity plus bounded.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 266, Theorem 9.10

import Mathlib
import Definitions.Def_TeschlODE_LocalBehavior_eigenvalues
import Definitions.Def_TeschlODE_LocalBehavior_spectralSubspace

namespace TeschlODE.LocalBehavior

/-- Teschl, Theorem 9.10, p. 266: let `A`, `B` be real `n × n` matrices with no eigenvalue on the
imaginary axis. If their stable subspaces `E₊(e^A)`, `E₊(e^B)` (generalized eigenvectors for
`Re < 0`) have equal dimensions and their unstable subspaces `E₋` (`Re > 0`) have equal
dimensions, then the flows are topologically conjugate (9.39): there is a homeomorphism `ϕ` of
`ℝⁿ` with `ϕ ∘ e^{tA} = e^{tB} ∘ ϕ` for every `t ∈ ℝ`. -/
theorem linear_flows_conjugate {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ z ∈ eigenvalues A, z.re ≠ 0) (hB : ∀ z ∈ eigenvalues B, z.re ≠ 0)
    (hs : Module.finrank ℝ (spectralSubspace A {z | z.re < 0}) =
      Module.finrank ℝ (spectralSubspace B {z | z.re < 0}))
    (hu : Module.finrank ℝ (spectralSubspace A {z | 0 < z.re}) =
      Module.finrank ℝ (spectralSubspace B {z | 0 < z.re})) :
    ∃ ϕ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ), ∀ (t : ℝ) (x : Fin n → ℝ),
      ϕ ((NormedSpace.exp (t • A)).mulVec x) = (NormedSpace.exp (t • B)).mulVec (ϕ x) := by sorry

end TeschlODE.LocalBehavior
