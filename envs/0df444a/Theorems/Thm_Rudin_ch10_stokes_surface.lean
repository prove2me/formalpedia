-- Prove2me | Theorems.Thm_Rudin_ch10_stokes_surface
-- name    : Rudin.ch10_stokes_surface
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T00:27:27.859697+00:00
-- url     : https://prove2.me/theorems/814a2a2f-f8f8-4ae6-b56a-92216265b3c2
-- title:
--   Stokes' theorem for a single $(m+1)$-surface
-- statement:
--   Stokes' theorem in the case of a chain consisting of a single surface with multiplicity one.
--
--   Let $V \subseteq \mathbb{R}^n$ be open, let $\Phi$ be an $(m+1)$-surface of class $C''$ with
--   parameter domain the standard simplex $Q^{m+1}$ and with $\Phi(Q^{m+1}) \subseteq V$, and let
--   $\omega$ be an $m$-form of class $C'$ in $V$. Then
--
--   $$\int_\Phi d\omega = \int_{\partial\Phi} \omega ,$$
--
--   where $\partial\Phi = \sum_{j=0}^{m+1} (-1)^j\,\Phi \circ (\text{$j$-th face of } [\mathbf{0}, \mathbf{e}_1, \dots, \mathbf{e}_{m+1}])$ is the boundary $m$-chain of $\Phi$ in the
--   sense of Rudin's Definition 10.30, and the right-hand side is the corresponding alternating sum of
--   integrals of $\omega$ over the faces.
--
--   This carries the whole analytic content of Rudin's Theorem 10.33: the passage from a single surface
--   to an arbitrary $(m+1)$-chain $\Psi = \sum_i c_i \Phi_i$ is the formal identity
--   $\int_\Psi = \sum_i c_i \int_{\Phi_i}$ together with the definition of the boundary of a chain.
--   Rudin proves the surface case by pulling $\omega$ back to the parameter simplex along $\Phi$, where
--   the exterior derivative is computed by the fundamental theorem of calculus and the iterated-integral
--   theorem, and the boundary terms are the faces of $Q^{m+1}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, Theorem 10.33 (Stokes' theorem) and Definition 10.30 (boundary of a chain), pp. 272-275

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.33 (Stokes' theorem) for a single surface: if `Φ` is a `(m+1)`-surface of
class `C''` with parameter domain `Q^{m+1}` whose values lie in an open set `V ⊆ ℝⁿ`, and `ω` is
an `m`-form of class `C'` in `V`, then the integral of `dω` over `Φ` equals the integral of `ω`
over the boundary chain `∂Φ`. -/
theorem ch10_stokes_surface (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V)
    (Φ : SimplexSurface (m + 1) n) (hΦ : ContDiff ℝ 2 Φ.map)
    (hΦV : ∀ u ∈ stdSimplex (m + 1), Φ.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    integralOverSimplex (extDeriv ω) Φ = Chain.integral ω (surfaceBoundary Φ) := by sorry

end Rudin
