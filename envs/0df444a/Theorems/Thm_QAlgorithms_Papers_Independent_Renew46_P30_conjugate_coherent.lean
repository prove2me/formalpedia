-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_conjugate_coherent
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.conjugate_coherent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:22:22.756228+00:00
-- url     : https://prove2.me/theorems/e7deb3e1-5d49-4f13-a6f5-eb0051877088
-- title:
--   §V.B.3: conjugate versus identical coherent pairs
-- statement:
--   For the coherent orbit $|z\rangle|\overline z\rangle$, use the concrete Weyl transform $T$ with number-ket coefficients $\overline{\langle m|D(w)|n\rangle}$. On the invariant oscillator Schwartz core, the functional $F(\psi)=\int(T\psi)(w)d^2w/\pi$ defines the positive constant-spectral-amplitude form $\overline{F(v)}F(w)$. Its covariant form integrates to a normalized operator measure on full Fock space and gives
--
--   $$p_{\mathrm{conj}}(\alpha\mid z)=4e^{-4|\alpha-z|^2},\qquad L_{\max}=4.$$
--
--   This maximum bounds every regular normalized covariant form defined on the input. The actual optimal identical-pair operator measure has $p_{\mathrm{id}}(\alpha\mid z)=2e^{-2|\alpha-z|^2}$. Their complex mean-square errors are $1/4$ and $1/2$, and each real quadrature variance is $1/8$ and $1/4$, respectively. For fidelity with a single estimated coherent state,
--
--   $$\mathbb E_{\mathrm{conj}}e^{-|\alpha-z|^2}=\frac45,\qquad\mathbb E_{\mathrm{id}}e^{-|\alpha-z|^2}=\frac23.$$
--
--   All displayed densities and moments have explicit integrability and normalization. The constant spectral amplitude is a functional, not an L² vector.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 7, §V.B.3: conjugate versus identical coherent pairs

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

/-- PDF p.7, §V.B.3: actual constant-amplitude positive form, normalized full-Fock
operator measure, pointwise Gaussian law and optimality. Fidelities are overlaps
with a single estimated coherent state, not with the two-mode product. -/
theorem conjugate_coherent :
    ∃ (T : MultiFock 2 ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 coherentMeasure)
      (A : FormSeed coherentMeasure (fun a : ℂ => ContinuousLinearMap.adjoint
        (multiDisplacement (Fin.cases a (fun _ => star a))))),
      (∀ n : Fin 2 → ℕ,
        (fun w : ℂ => T (multiKet n) w) =ᵐ[coherentMeasure]
          (fun w => star (displacementMatrix w (n 0) (n 1)))) ∧
      (A.domain : Set (MultiFock 2)) = {v | OscillatorSchwartz v} ∧
      (∀ v, v ∈ A.domain → Integrable (fun w : ℂ => T v w) coherentMeasure) ∧
      (∀ v w, v ∈ A.domain → w ∈ A.domain →
        A.form v w = star (spectralFunctional T v) * spectralFunctional T w) ∧
      (∀ z : ℂ, displacedVacuumPair z (star z) ∈ A.domain ∧
        (∀ a, formDensity A (displacedVacuumPair z (star z)) a = gaussianDensity 4 z a)) ∧
      (∀ B : FormSeed coherentMeasure (fun a : ℂ => ContinuousLinearMap.adjoint
        (multiDisplacement (Fin.cases a (fun _ => star a)))),
        multiKet (fun _ : Fin 2 => 0) ∈ B.domain →
          (B.form (multiKet (fun _ => 0)) (multiKet (fun _ => 0))).re ≤ 4) ∧
      (∃ avg : HilbertOperatorMeasure ℂ (MultiFock 2),
        (∀ E : Set ℂ, MeasurableSet E →
          WeakIntegral (coherentMeasure.restrict E)
            (multiOrbit (numberSeed 1 (fun _ => 0))) (avg.effect E)) ∧
        (∀ z : ℂ, ∀ E : Set ℂ, MeasurableSet E →
          pureSeedDensity (avg.effect E) (displacedVacuumPair z z) =
            ∫ a in E, gaussianDensity 2 z a ∂coherentMeasure)) ∧
      (∀ z : ℂ,
        Integrable (gaussianDensity 2 z) coherentMeasure ∧
        Integrable (gaussianDensity 4 z) coherentMeasure ∧
        (∫ a, gaussianDensity 2 z a ∂coherentMeasure) = 1 ∧
        (∫ a, gaussianDensity 4 z a ∂coherentMeasure) = 1 ∧
        Integrable (fun a => Complex.normSq (a - z) * gaussianDensity 2 z a) coherentMeasure ∧
        Integrable (fun a => Complex.normSq (a - z) * gaussianDensity 4 z a) coherentMeasure ∧
        (∫ a, Complex.normSq (a - z) * gaussianDensity 2 z a ∂coherentMeasure) = 1 / 2 ∧
        (∫ a, Complex.normSq (a - z) * gaussianDensity 4 z a ∂coherentMeasure) = 1 / 4 ∧
        (∀ coordinate : ℂ →L[ℝ] ℝ, (coordinate = Complex.reCLM ∨ coordinate = Complex.imCLM) →
          Integrable (fun a => (coordinate (a - z)) ^ 2 * gaussianDensity 2 z a) coherentMeasure ∧
          Integrable (fun a => (coordinate (a - z)) ^ 2 * gaussianDensity 4 z a) coherentMeasure ∧
          (∫ a, (coordinate (a - z)) ^ 2 * gaussianDensity 2 z a ∂coherentMeasure) = 1 / 4 ∧
          (∫ a, (coordinate (a - z)) ^ 2 * gaussianDensity 4 z a ∂coherentMeasure) = 1 / 8) ∧
        Integrable (fun a => Real.exp (-Complex.normSq (a - z)) * gaussianDensity 2 z a) coherentMeasure ∧
        Integrable (fun a => Real.exp (-Complex.normSq (a - z)) * gaussianDensity 4 z a) coherentMeasure ∧
        (∫ a, Real.exp (-Complex.normSq (a - z)) * gaussianDensity 2 z a ∂coherentMeasure) = 2 / 3 ∧
        (∫ a, Real.exp (-Complex.normSq (a - z)) * gaussianDensity 4 z a ∂coherentMeasure) = 4 / 5) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
