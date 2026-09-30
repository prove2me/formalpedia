-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_extension_hilbert_polynomial
-- name    : WeierstrassEllipticZeta.projective_extension_hilbert_polynomial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T06:31:25.726497+00:00
-- url     : https://prove2.me/theorems/03ab061f-86f0-4d3a-be1b-2b0ba224b5ed
-- title:
--   The Weierstrass extension surface has Hilbert polynomial 3n² + 2
-- statement:
--   Let $L$ be a complex period lattice with its normalized entire Weierstrass coordinates and a coordinate-compatible group realization of its graph quotient as the projective extension surface $E\subset\mathbf P^4$. The Hilbert polynomial of the actual homogeneous vanishing ideal of $E$ is $$P_E(n)=3n^2+2.$$ In particular, the projective closure of $E$ has Hilbert dimension two. The coordinate realization hypotheses are stated explicitly in the formalization; no dimension or Hilbert-polynomial hypothesis is assumed.
-- source:
--   Application geometry for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. Supporting comparison for the actual Hilbert-dimension convention of Philippon Section 3; not a new numbered result of Philippon.

import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open MvPolynomial TranscendenceTheory PhilipponMultiplicity WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.projective_extension_hilbert_polynomial
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
    Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) =
      C 3 * X 0 ^ 2 + C 2 := by sorry
