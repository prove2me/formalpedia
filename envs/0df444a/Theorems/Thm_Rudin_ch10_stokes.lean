-- Prove2me | Theorems.Thm_Rudin_ch10_stokes
-- name    : Rudin.ch10_stokes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:31:13.159773+00:00
-- url     : https://prove2.me/theorems/b16d2d9e-3b94-4d44-90e2-145feab86d99
-- title:
--   Theorem 10.33 — Stokes' theorem
-- statement:
--   If $\Psi$ is a $k$-chain of class $C''$ in an open set $V \subseteq \mathbb{R}^n$ and $\omega$ is a $(k-1)$-form of class $C'$ in $V$, then $\int_\Psi d\omega = \int_{\partial\Psi}\omega$. Special cases are the fundamental theorem of calculus, Green's theorem, the divergence theorem and the classical theorem of Stokes.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 272, Theorem 10.33

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.33 (Stokes' theorem): if `Ψ` is a `(m+1)`-chain of class `C''` in an open
set `V ⊆ ℝⁿ` and `ω` is an `m`-form of class `C'` in `V`, then the integral of `dω` over
`Ψ` equals the integral of `ω` over the boundary `∂Ψ`. -/
theorem ch10_stokes (m n : ℕ) (V : Set (Fin n → ℝ)) (hV : IsOpen V) (Ψ : Chain (m + 1) n)
    (hΨ : ∀ t ∈ Ψ.terms, ContDiff ℝ 2 t.2.map ∧ ∀ u ∈ stdSimplex (m + 1), t.2.map u ∈ V)
    (ω : KForm m n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) V) :
    Chain.integral (extDeriv ω) Ψ = Chain.integral ω Ψ.boundary := by sorry

end Rudin
