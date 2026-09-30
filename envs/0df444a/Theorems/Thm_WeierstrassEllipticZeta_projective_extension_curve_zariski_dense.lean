-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_projective_extension_curve_zariski_dense
-- name    : WeierstrassEllipticZeta.projective_extension_curve_zariski_dense
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T06:44:29.964331+00:00
-- url     : https://prove2.me/theorems/e1a4188c-730b-4caf-8169-3d5116d85ab7
-- title:
--   The Weierstrass curve is Zariski dense in the additive-extension product
-- statement:
--   Let $L$ be a complex period lattice, let $S_0,\ldots,S_4$ be its normalized entire Weierstrass coordinates, and let $e$ be a coordinate-compatible identification of the graph quotient with its projective extension $E$. Then $$\overline{\{(z,e([(z,0)])):z\in\mathbf C\}}^{\mathrm{Zar}}=\mathbf G_a\times E.$$ The topology is the one induced by the actual embedding in $\mathbf P^1\times\mathbf P^4$, and the statement includes the extension fibers above lattice parameters.
-- source:
--   Application geometry for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. Application of the curve-relation criterion to the actual multiprojective Zariski topology; not a new numbered result of Philippon.

import Definitions.Def_PhilipponMultiplicity_Hilbert
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open MvPolynomial TranscendenceTheory PhilipponMultiplicity WeierstrassEllipticZeta

theorem WeierstrassEllipticZeta.projective_extension_curve_zariski_dense
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
    let M : MultiProjectiveSpace ℂ := ⟨2, by decide, ![1, 4]⟩
    let embedding : (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃) → M.Point :=
      fun p => Fin.cons
        (Projectivization.mk ℂ ![1, p.1]
          (by intro h; have hh := congrFun h 0; simpa using hh))
        (Fin.cons p.2.val.val (fun i => Fin.elim0 i))
    @Dense (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃)
      (TopologicalSpace.induced embedding M.zariskiTopology)
      (Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph L.lattice η).mkQ (z, 0))))) := by sorry
