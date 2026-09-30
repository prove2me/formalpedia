-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_extension_group_with_regular_negation
-- name    : WeierstrassEllipticZeta.projective_extension_group_with_regular_negation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T23:31:15.537425+00:00
-- url     : https://prove2.me/theorems/5574ea1f-7cbd-4cc2-99bd-0e8d3787e836
-- title:
--   Projective extension group and regular inversion
-- statement:
--   Let $L$ be a complex period lattice, let $\sigma$ satisfy the normalized sigma differential data, and let five entire functions $S_j$ have no common zero and agree off the lattice with
--
--   $$\sigma(z)^3(1,\wp(z),\wp'(z),\zeta(z),\wp'(z)\zeta(z)+2\wp(z)^2).$$
--
--   Let $\eta$ be the additive quasiperiod map. The explicit two-chart quadratic–cubic projective surface admits a commutative group structure and an additive equivalence from $\mathbb C^2/\{(\omega,-\eta(\omega))\}$. The equivalence sends $[(z,u)]$ to
--
--   $$[S_0(z):S_1(z):S_2(z):S_3(z)+uS_0(z):S_4(z)+uS_2(z)].$$
--
--   Inversion in this group is regular in the projective embedding. This statement does not assert regularity of addition, a Hilbert dimension, or the completed Philippon model.
-- source:
--   Application geometry for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X; explicit supporting construction, not an additional numbered result of Philippon. Regularity uses Philippon (1986), §2, https://numdam.org/articles/10.24033/bsmf.2060/.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity WeierstrassEllipticZeta TranscendenceTheory

theorem WeierstrassEllipticZeta.projective_extension_group_with_regular_negation
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
          (PhilipponMultiplicity.projectiveSpace ℂ 4) (PhilipponMultiplicity.projectiveSpace ℂ 4)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => x.val.val)
          (fun x : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => (-x).val.val) := by sorry
