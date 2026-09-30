-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_philippon_model_from_hilbert_and_dense_extension
-- name    : WeierstrassEllipticZeta.philippon_model_from_hilbert_and_dense_extension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T07:13:56.551795+00:00
-- url     : https://prove2.me/theorems/a01fb2ba-86ff-43ee-bef7-85d1e4c235ce
-- title:
--   Complete the analytic model from the regular dense extension with computed Hilbert dimensions
-- statement:
--   Let $L$ be a complex period lattice and $S$ its normalized entire Weierstrass coordinates. Suppose its graph quotient has been identified with the actual projective extension $E$, with regular group operations. Assume the established Hilbert polynomials $P_{\mathbf G_a}(n)=n+1$ and $P_E(n)=3n^2+2$, and the established density of $z\mapsto(z,e([(z,0)]))$ in $\mathbf G_a\times E$. Then these data admit a Philippon application model with a compatible local analytic subgroup of dimension one, translated analytic lifts, and the required exact polynomial pullback and zero-locus identities.
-- source:
--   Remaining application construction for Senthil Kumar, Appendix A, https://doi.org/10.1017/S001309152610145X. This is application work in Senthil, not a result of Philippon's paper.

import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
set_option autoImplicit false
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity


open MvPolynomial

theorem WeierstrassEllipticZeta.philippon_model_from_hilbert_and_dense_extension
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
      (fun x => fun _ => (-x).val.val))
    (hGa : Hilbert.hilbertPolynomial ℂ 1 (fun _ => 1)
      ((projectiveSpace ℂ 1).vanishingIdeal
        ((fun p : Projectivization ℂ (Fin 2 → ℂ) => fun _ : Fin 1 => p) ''
          {p : Projectivization ℂ (Fin 2 → ℂ) | p.rep 0 ≠ 0})) =
      MvPolynomial.X 0 + 1)
    (hExtensionHilbert : Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) =
      C 3 * X 0 ^ 2 + C 2)
    (hCurveDense : let M : MultiProjectiveSpace ℂ := ⟨2, by decide, ![1, 4]⟩
    let embedding : (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃) → M.Point :=
      fun p => Fin.cons
        (Projectivization.mk ℂ ![1, p.1]
          (by intro h; have hh := congrFun h 0; simpa using hh))
        (Fin.cons p.2.val.val (fun i => Fin.elim0 i))
    @Dense (ℂ × ProjectiveExtensionChartLocus L.g₂ L.g₃)
      (TopologicalSpace.induced embedding M.zariskiTopology)
      (Set.range (fun z : ℂ => (z, e ((extensionPeriodGraph L.lattice η).mkQ (z, 0)))))) :
    Nonempty (WeierstrassEllipticZeta.PhilipponApplication.Model S) := by sorry
