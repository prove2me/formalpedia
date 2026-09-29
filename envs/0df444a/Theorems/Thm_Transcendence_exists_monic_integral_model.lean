-- Prove2me | Theorems.Thm_Transcendence_exists_monic_integral_model
-- name    : Transcendence.exists_monic_integral_model
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:47.145239+00:00
-- url     : https://prove2.me/theorems/f61d5666-eeac-4d3e-b3fd-81eba3d5f7a0
-- title:
--   A monic integral model of a simple algebraic extension of ℚ(ω)
-- statement:
--   Let $\omega \in \mathbb{C}$ be transcendental and let $\theta \in \mathbb{C}$ be algebraic over $\mathbb{Q}(\omega)$. Then there are $\omega_1 \in \mathbb{C}$ and $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of positive degree $d$, with $Q(\omega, \omega_1) = 0$ and minimal there: no non-zero $A \in \mathbb{Z}[X][Y]$ of $Y$-degree less than $d$ vanishes at $(\omega, \omega_1)$, together with $v \in \mathbb{Z}[X]$ such that $v(\omega) \neq 0$ and $\omega_1 = v(\omega)\,\theta$.
--
--   Clear the denominators of the minimal polynomial of $\theta$ over $\mathbb{Q}(\omega)$ with one $v \in \mathbb{Z}[X]$ and rescale $\theta$. A pair $(\omega, \omega_1)$ with such a $Q$ is the setting the four exponentials nodes assume.
-- source:
--   Standard. The normalisation at the start of §III of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- A monic integral model of a simple algebraic extension of `ℚ(ω)`.

Let `ω` be transcendental and `θ` algebraic over `ℚ(ω)`, with minimal polynomial `m` of degree `d`.
Clearing the denominators of the coefficients of `m` with one `v ∈ ℤ[X]`, and rescaling
`ω₁ = v(ω) θ`, gives a polynomial `Q ∈ ℤ[X][Y]`, monic of degree `d` in `Y`, with `Q(ω, ω₁) = 0`.
Since `ω₁` also has degree `d` over `ℚ(ω)` and `ω` is transcendental, no non-zero `A ∈ ℤ[X][Y]` of
`Y`-degree below `d` vanishes at `(ω, ω₁)`. -/
theorem exists_monic_integral_model (ω θ : ℂ) (hω : Transcendental ℚ ω)
    (hθ : IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) θ) :
    ∃ (ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)), Q.Monic ∧ 0 < Q.natDegree ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
      (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
      ∃ v : Polynomial ℤ, Polynomial.aeval ω v ≠ 0 ∧ ω₁ = Polynomial.aeval ω v * θ := by
  sorry

end Transcendence
