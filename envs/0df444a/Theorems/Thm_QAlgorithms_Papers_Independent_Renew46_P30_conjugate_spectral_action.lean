-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_conjugate_spectral_action
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.conjugate_spectral_action
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:21:42.794662+00:00
-- url     : https://prove2.me/theorems/f784efae-63b0-4152-8e85-7cd78d00fc70
-- title:
--   §V.B.3: continuous Weyl spectral realization
-- statement:
--   For the full two-mode representation $D(z)\otimes D(\overline z)$, there is a concrete unitary Weyl transform $T$ from completed Fock space onto the nonatomic space $L^2(\mathbb C,d^2w/\pi)$, specified on every number ket by
--
--   $$T|m,n\rangle(w)=\overline{\langle m|D(w)|n\rangle}.$$
--
--   For every Hilbert vector $\psi$ and displacement $z$, its intertwining law holds almost everywhere:
--
--   $$T[(D(z)\otimes D(\overline z))\psi](w)=e^{z\overline w-\overline z w}(T\psi)(w).$$
--
--   The representation has no nonzero closed irreducible invariant summand in the physical Hilbert space. The characters are direct-integral fibers, not normalizable eigenvectors. No unrestricted twirling or full commutant theorem is asserted here.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.3: continuous Weyl spectral realization

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P30

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39 (IsTraceClass)

open QAlgorithms.Papers.Independent.Claimed50.P14 (SU)

open QAlgorithms.Papers.Independent.Claimed50.P17 (pairAction)

open scoped ComplexConjugate ComplexOrder Manifold ContDiff ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (R : CovariantHilbertData G H)

variable {M : Type*} [DecidableEq M]

variable (D : Components R M)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet displacement displacementMatrix coherentMeasure coherentKet)

variable {J : Type*} [DecidableEq J]

/-- PDF pp.6–7, §V.B.3: concrete nonatomic Weyl/Plancherel realization on completed
L²(C,d²w/pi). The basis coefficient has conjugation on the bra. No atomic lp(C)
or unrestricted continuous twirling assertion is substituted for this result. -/
theorem conjugate_spectral_action :
    MultiWeylRealized 2 ∧
    ∃ T : MultiFock 2 ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 coherentMeasure,
      (∀ n : Fin 2 → ℕ,
        (fun w : ℂ => T (multiKet n) w) =ᵐ[coherentMeasure]
          (fun w => star (displacementMatrix w (n 0) (n 1)))) ∧
      (∀ z : ℂ, ∀ psi : MultiFock 2,
        (fun w : ℂ => T (multiDisplacement (Fin.cases z (fun _ => star z)) psi) w) =ᵐ[coherentMeasure]
          (fun w => Complex.exp (z * star w - star z * w) * T psi w)) ∧
      (∀ W : Submodule ℂ (MultiFock 2), IsClosed (W : Set (MultiFock 2)) →
        (∀ z v, v ∈ W → multiDisplacement (Fin.cases z (fun _ => star z)) v ∈ W) →
        (∀ L : Submodule ℂ (MultiFock 2), IsClosed (L : Set (MultiFock 2)) → L ≤ W →
          (∀ z v, v ∈ L → multiDisplacement (Fin.cases z (fun _ => star z)) v ∈ L) →
          L = ⊥ ∨ L = W) → W = ⊥) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
