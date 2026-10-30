-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_polar_normalization_covariant
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.polar_normalization_covariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:13:44.191993+00:00
-- url     : https://prove2.me/theorems/84d34b91-2637-449a-b56e-75d9265c1d40
-- title:
--   Appendix B: polar normalization preserves covariance
-- statement:
--   Let $G$ be finite, $d=|G|$, and $n\ge1$. Let $\Psi$ be a normalized invariant vector in $\mathcal H_G^{\otimes(n+1)}$ under the diagonal left regular action. Define $E_{z,x}=\sqrt d\,\Psi_{x,z}$, using the source's unnormalized maximally entangled contraction. If $E^\dagger E$ is positive definite, define
--   $$T=E(E^\dagger E)^{-1/2}.$$
--   Then
--   $$T^\dagger T=I,\qquad U(g)^{\otimes n}E=EU(g),\qquad U(g)^{\otimes n}T=TU(g)\quad(\forall g\in G).$$
--   Thus polar normalization produces a covariant isometry on its full-rank domain. Full rank is a pointwise domain condition here; the random theorem separately asserts that this locus has probability one.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 9, Appendix B: polar normalization preserves covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.8--9: pointwise polar normalization is a covariant isometry on
its full-rank domain. No almost-sure full-rank hypothesis is substituted for this domain. -/
theorem polar_normalization_covariant
    {G : Type} [Group G] [Fintype G] {n : ℕ} (hn : 1 ≤ n)
    (ψ : EuclideanSpace ℂ (Fin (n + 1) → G))
    (hstate : IsState ψ) (hinv : RegularInvariant ψ)
    (hfull : ((reshapedEncoder ψ)ᴴ * reshapedEncoder ψ).PosDef) :
    (polarEncoder ψ)ᴴ * polarEncoder ψ = 1 ∧
    (∀ g, localTensorMatrix (fun _ : Fin n => groupLeftRegular g) * reshapedEncoder ψ =
      reshapedEncoder ψ * groupLeftRegular g) ∧
    (∀ g, localTensorMatrix (fun _ : Fin n => groupLeftRegular g) * polarEncoder ψ =
      polarEncoder ψ * groupLeftRegular g) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
