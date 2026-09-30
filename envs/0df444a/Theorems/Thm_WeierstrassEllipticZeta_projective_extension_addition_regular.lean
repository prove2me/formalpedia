-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_extension_addition_regular
-- name    : WeierstrassEllipticZeta.projective_extension_addition_regular
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T04:48:40.630981+00:00
-- url     : https://prove2.me/theorems/ed94884e-1dda-4c71-818f-b30e7e5f7a6d
-- title:
--   Regularity of the full Weierstrass extension addition operation
-- statement:
--   For normalized entire Weierstrass coordinates with no common zero, assume the specified coordinate-compatible additive equivalence from the period-graph quotient to the quadratic–cubic projective extension. Then the full two-variable addition map of this extension is regular in the multiprojective polynomial sense, at every pair of points. The conclusion includes affine equal-base pairs, inverse pairs, and points above the elliptic identity. No regularity of addition is assumed.
-- source:
--   Application geometry for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. Explicit construction of the regular group operations for the stated algebraic-group embedding. The affine formulas come from equations (5)–(6); the complete chart atlas and its coverage are proved here. Not a numbered result of Philippon.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity

theorem WeierstrassEllipticZeta.projective_extension_addition_regular
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

 :
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun pq : ProjectiveExtensionChartLocus L.g₂ L.g₃ ×
          ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then pq.1.val.val else pq.2.val.val)
      (fun pq => fun _ => (pq.1 + pq.2).val.val) := by sorry
