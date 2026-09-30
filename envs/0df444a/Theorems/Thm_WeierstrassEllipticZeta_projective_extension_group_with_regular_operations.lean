-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_operations
-- name    : WeierstrassEllipticZeta.projective_extension_group_with_regular_operations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T04:49:00.725868+00:00
-- url     : https://prove2.me/theorems/85b168f6-894a-408e-b1ee-a875a4bba93f
-- title:
--   The Weierstrass extension group has regular addition and inversion
-- statement:
--   Let normalized entire Weierstrass coordinates have no common zero, and let the lattice homomorphism equal the zeta quasi-period. The explicit quadratic–cubic projective extension admits a commutative group structure and a coordinate-compatible additive equivalence with the period-graph quotient, for which both addition and inversion are regular. Neither group operation is assumed regular. This supplies the group-operation fields needed for the Senthil application to Philippon; it does not assert the remaining Hilbert-dimension or density fields.
-- source:
--   Application geometry for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. Explicit construction of the regular group operations for the stated algebraic-group embedding. The affine formulas come from equations (5)–(6); the complete chart atlas and its coverage are proved here. Not a numbered result of Philippon.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity

theorem WeierstrassEllipticZeta.projective_extension_group_with_regular_operations
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ group : AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃),
      letI := group
      ∃ e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃,
        (∀ z u : ℂ, ∃ hv :
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
          (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
            ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSquare ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
            fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
          (fun xy => fun _ => (xy.1 + xy.2).val.val) ∧
        PhilipponMultiplicity.MultiProjectiveSpace.IsRegularAlong
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by sorry
