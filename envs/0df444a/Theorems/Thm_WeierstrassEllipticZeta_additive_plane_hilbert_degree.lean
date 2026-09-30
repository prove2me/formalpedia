-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_additive_plane_hilbert_degree
-- name    : WeierstrassEllipticZeta.additive_plane_hilbert_degree
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T21:08:46.277128+00:00
-- url     : https://prove2.me/theorems/f664c201-76f6-46ac-8489-872ff86ccf7b
-- title:
--   Weierstrass plane in the additive plane: exact Hilbert degree
-- statement:
--   Let p(t,u) in P¹ × P⁴ have homogeneous coordinates ([1:t], [0:0:1:0:ρ+u]). For every pair of natural block degrees (m,n), the actual factorial-normalized Hilbert degree of its image is 2mn. The proof establishes the complete quotient Hilbert function (m+1)(n+1), including all zero block degrees, and hence the genuine Hilbert polynomial. This is the additive plane occurring in the Weierstrass application.
-- source:
--   Supporting degree computation for Lemma A.1 and Proposition A.1 of the Senthil Kumar mission; https://doi.org/10.1017/S001309152610145X, Appendix A.

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PhilipponMultiplicity MvPolynomial

theorem WeierstrassEllipticZeta.additive_plane_hilbert_degree (ρ : ℂ)
    (p : (Fin 2 → ℂ) → (@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).Point)
    (hp : ∀ t, (∃ h : ![1, t 0] ≠ (0 : Fin 2 → ℂ),
        Projectivization.mk ℂ ![1, t 0] h = p t (0 : Fin 2)) ∧
      (∃ h : ![0, 0, 1, 0, ρ + t 1] ≠ (0 : Fin 5 → ℂ),
        Projectivization.mk ℂ ![0, 0, 1, 0, ρ + t 1] h = p t (1 : Fin 2))) (D : Fin 2 → ℕ) :
    Hilbert.degreeValue ℂ 2 ![1, 4]
      ((@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).vanishingIdeal (Set.range p)) D = 2 * (D 0 : ℚ) * (D 1 : ℚ) := by sorry
