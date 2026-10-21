-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_identical_reduction
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_identical_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:16:03.091995+00:00
-- url     : https://prove2.me/theorems/c0ca26cb-21ff-4a67-b042-1f78c8977f18
-- title:
--   §V.B.2: N-mode concentration and irreducible subspaces
-- statement:
--   Let $N=r+1>1$ oscillators undergo identical displacements $D(z)^{\otimes N}$. On the full completed Fock space construct the passive mode rotation $V$ from the printed generator with $\phi_N=\arctan\sqrt{N-1}/\sqrt{N-1}$. It is a unitary extension of its finite number-sector coefficients, and
--
--   $$V D(z)^{\otimes N}V^\dagger=D(\sqrt N z)\otimes I^{\otimes(N-1)}.$$
--
--   For every complete orthonormal spectator basis $\{\Phi_j\}$, the closed spaces $\mathcal H_j=V^\dagger(\mathcal H\otimes\Phi_j)$ are mutually orthogonal, have closed span equal to the full Hilbert space, and are invariant and irreducible. Their isometric onto intertwiners are $V^\dagger(I\otimes|\Phi_i\rangle\langle\Phi_j|)V$. The actual coefficient-square Haar integral for each component is $b_j=1/N$ relative to $d^2z/\pi$. This is the full multiplicity decomposition, rather than just a two-mode special case.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2: N-mode concentration and irreducible subspaces

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

/-- PDF p.6, §V.B.2: full concentration, exhaustive irreducible multiplicity
subspaces with dense algebraic sum, coherent intertwiners and actual
coefficient-square integral 1/N.
Here r=N-1>0, so the angle denominator is never zero. -/
theorem wh_identical_reduction (r : ℕ) (hr : 0 < r) :
    MultiWeylRealized (r + 1) ∧
    concentrationMatrix r = NormedSpace.exp (concentrationGenerator r) ∧
    (∀ m n, fockConcentration r (multiKet n) m = passiveEntry (concentrationMatrix r) m n) ∧
    (∃ V : MultiFock (r + 1) ≃ₗᵢ[ℂ] MultiFock (r + 1),
      ∀ v, V v = fockConcentration r v) ∧
    (∀ (v : Fock) (w : MultiFock r) n,
      splitVector r v w n = v (n 0) * w (fun j => n j.succ)) ∧
    (∀ z : ℂ,
      (fockConcentration r).comp ((multiDisplacement (fun _ => z)).comp
        (ContinuousLinearMap.adjoint (fockConcentration r))) =
      multiDisplacement (fun j => if j.val = 0 then (Real.sqrt (r + 1) : ℂ) * z else 0)) ∧
    (∀ (J : Type) [Countable J] [DecidableEq J]
      (b : HilbertBasis J ℂ (MultiFock r)),
      (∀ i j v w, i ≠ j → v ∈ oscillatorComponent r (b i) →
        w ∈ oscillatorComponent r (b j) → inner ℂ v w = 0) ∧
      (⨆ j, oscillatorComponent r (b j)).topologicalClosure = ⊤ ∧
      (∀ j z v, v ∈ oscillatorComponent r (b j) →
        multiDisplacement (fun _ => z) v ∈ oscillatorComponent r (b j)) ∧
      (∀ j (W : Submodule ℂ (MultiFock (r + 1))), IsClosed (W : Set (MultiFock (r + 1))) →
        W ≤ oscillatorComponent r (b j) →
        (∀ z v, v ∈ W → multiDisplacement (fun _ => z) v ∈ W) →
        W = ⊥ ∨ W = oscillatorComponent r (b j)) ∧
      (∀ (i j : J) (v : MultiFock (r + 1)), v ∈ oscillatorComponent r (b j) →
        ‖oscillatorIntertwiner r (b i) (b j) v‖ = ‖v‖ ∧
        oscillatorIntertwiner r (b i) (b j) v ∈ oscillatorComponent r (b i)) ∧
      (∀ i j w, w ∈ oscillatorComponent r (b i) →
        ∃ v ∈ oscillatorComponent r (b j), oscillatorIntertwiner r (b i) (b j) v = w) ∧
      (∀ i j z, (oscillatorIntertwiner r (b i) (b j)).comp (multiDisplacement (fun _ => z)) =
        (multiDisplacement (fun _ => z)).comp (oscillatorIntertwiner r (b i) (b j))) ∧
      (∀ j,
        let v := ContinuousLinearMap.adjoint (fockConcentration r) (splitVector r (fockKet 0) (b j))
        Integrable (fun z => ‖inner ℂ v (multiDisplacement (fun _ => z) v)‖ ^ 2) coherentMeasure ∧
        (∫ z, ‖inner ℂ v (multiDisplacement (fun _ => z) v)‖ ^ 2 ∂coherentMeasure) =
          ((r + 1 : ℕ) : ℝ)⁻¹)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
