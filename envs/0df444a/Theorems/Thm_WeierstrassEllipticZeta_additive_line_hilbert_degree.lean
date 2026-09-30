-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_additive_line_hilbert_degree
-- name    : WeierstrassEllipticZeta.additive_line_hilbert_degree
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T21:08:38.090641+00:00
-- url     : https://prove2.me/theorems/537c277e-a621-4aee-9d22-cefaba395fc8
-- title:
--   Weierstrass line in the additive plane: exact Hilbert degree
-- statement:
--   Let p(t) in the product of projective spaces P¹ × P⁴ have homogeneous coordinates ([1:a t], [0:0:1:0:ρ+b t]), where a and b are not both zero. For every pair of natural block degrees (m,n), its actual factorial-normalized Hilbert degree is m when b=0, n when a=0, and m+n when both are nonzero. The parameter ρ allows an arbitrary choice of origin in the vertical affine chart. The degree is computed from the multigraded quotient by the homogeneous vanishing ideal.
-- source:
--   Supporting degree computation for Lemma A.1 and Proposition A.1 of the Senthil Kumar mission; https://doi.org/10.1017/S001309152610145X, Appendix A.

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open PhilipponMultiplicity MvPolynomial

theorem WeierstrassEllipticZeta.additive_line_hilbert_degree (a b ρ : ℂ) (hne : a ≠ 0 ∨ b ≠ 0)
    (p : ℂ → (@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).Point)
    (hp : ∀ t, (∃ h : ![1, a * t] ≠ (0 : Fin 2 → ℂ),
        Projectivization.mk ℂ ![1, a * t] h = p t (0 : Fin 2)) ∧
      (∃ h : ![0, 0, 1, 0, ρ + b * t] ≠ (0 : Fin 5 → ℂ),
        Projectivization.mk ℂ ![0, 0, 1, 0, ρ + b * t] h = p t (1 : Fin 2))) (D : Fin 2 → ℕ) :
    Hilbert.degreeValue ℂ 2 ![1, 4]
      ((@MultiProjectiveSpace.mk ℂ 2 (by decide) ![1, 4]).vanishingIdeal (Set.range p)) D =
        (if a = 0 then 0 else (D 0 : ℚ)) + (if b = 0 then 0 else (D 1 : ℚ)) := by sorry
