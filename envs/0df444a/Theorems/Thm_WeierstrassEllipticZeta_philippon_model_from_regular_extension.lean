-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_model_from_regular_extension
-- name    : WeierstrassEllipticZeta.philippon_model_from_regular_extension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T05:01:33.030991+00:00
-- url     : https://prove2.me/theorems/6fa0b399-40f3-4c4a-9d33-1097c305cbdf
-- title:
--   Assembling the Philippon model from the regular Weierstrass extension
-- statement:
--   Let $S$ be the normalized entire Weierstrass coordinate tuple, with no common zero. Suppose the period-graph quotient is identified with the explicit quadratic–cubic projective extension by the prescribed coordinate formula, and addition and inversion are regular. Then these data admit a Philippon application model: two embedded group factors of actual Hilbert dimensions $1$ and $2$, an injective Zariski-dense complex curve, a one-dimensional analytic subgroup with that carrier, and the specified homogeneous-coordinate and pullback identities. This is the remaining geometric and analytic assembly result after the group operations have been constructed.
-- source:
--   Senthil Kumar, Appendix A (especially the algebraic-group realization and analytic curve in A.2), https://doi.org/10.1017/S001309152610145X. Application lemma for Senthil, not a result of Philippon.

import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity

theorem WeierstrassEllipticZeta.philippon_model_from_regular_extension
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ) (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)


    (hadd : MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun xy : ProjectiveExtensionChartLocus L.g₂ L.g₃ × ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then xy.1.val.val else xy.2.val.val)
      (fun xy => fun _ => (xy.1 + xy.2).val.val))
    (hneg : MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
      (fun x => fun _ => (-x).val.val)) :
    Nonempty (WeierstrassEllipticZeta.PhilipponApplication.Model S) := by sorry
