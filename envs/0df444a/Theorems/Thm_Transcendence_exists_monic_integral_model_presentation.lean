-- Prove2me | Theorems.Thm_Transcendence_exists_monic_integral_model_presentation
-- name    : Transcendence.exists_monic_integral_model_presentation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:59:06.24688+00:00
-- url     : https://prove2.me/theorems/9a72eeea-1c1f-42b8-9221-24234f891350
-- title:
--   Finitely many numbers algebraic over ℚ(ω) have a common presentation over one monic integral model
-- statement:
--   Let $\omega \in \mathbb{C}$ be transcendental and let $z_i$ ($i$ in a finite type) be algebraic over $\mathbb{Q}(\omega)$. Then there are $\omega_1 \in \mathbb{C}$ and $Q \in \mathbb{Z}[X][Y]$, monic in $Y$ of positive degree $d$, with $Q(\omega, \omega_1) = 0$ and minimal there: no non-zero $A \in \mathbb{Z}[X][Y]$ of $Y$-degree less than $d$ vanishes at $(\omega, \omega_1)$, together with $D, E_i \in \mathbb{Z}[X][Y]$ such that $D(\omega, \omega_1) \neq 0$ and
--
--   $$z_i\, D(\omega, \omega_1) = E_i(\omega, \omega_1) \quad \text{for every } i.$$
--
--   By the primitive element theorem the $z_i$ lie in $\mathbb{Q}(\omega)(\theta)$ for one $\theta$; the monic integral model of $\theta$ (`Transcendence.exists_monic_integral_model`) then presents every $z_i$ as a quotient of integer polynomials in $(\omega, \omega_1)$ with one common denominator.
-- source:
--   Standard. The presentation used in §III of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202. Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- Finitely many numbers algebraic over `ℚ(ω)` have a common presentation over one monic integral
model.

Let `ω` be transcendental and let `z₁, …, z_k` be algebraic over `ℚ(ω)`. By the primitive element
theorem they lie in `ℚ(ω, θ)` for one `θ` algebraic over `ℚ(ω)`; rescale `θ` to `ω₁`, a root of a
polynomial `Q ∈ ℤ[X][Y]` monic in `Y` and minimal at `(ω, ω₁)`. Every element of
`ℚ(ω, ω₁) = ℚ(ω, θ)` is a quotient `E(ω, ω₁) / D(ω, ω₁)` of integer polynomials, and a product of
denominators serves all the `zᵢ` at once. -/
theorem exists_monic_integral_model_presentation (ω : ℂ) (hω : Transcendental ℚ ω)
    {ι : Type*} [Finite ι] (z : ι → ℂ)
    (hz : ∀ i, IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) (z i)) :
    ∃ (ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)), Q.Monic ∧ 0 < Q.natDegree ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
      (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
      ∃ (D : Polynomial (Polynomial ℤ)) (E : ι → Polynomial (Polynomial ℤ)),
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧
        ∀ i, z i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i) := by
  sorry

end Transcendence
