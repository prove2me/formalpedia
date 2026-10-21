-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_coherent_local
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_coherent_local
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:19:19.196273+00:00
-- url     : https://prove2.me/theorems/1736d59e-cb48-49b2-93f9-662c95eab77f
-- title:
--   §V.B.2(i): two local optimal coherent-state measurements
-- statement:
--   On the full two-mode orbit $|z\rangle|z\rangle$, consider two independent heterodyne measurements followed by their arithmetic mean, and the joint measurement of $Q_1=(a_1+a_1^\dagger)/2$ and $P_2=(a_2-a_2^\dagger)/(2i)$ with output $\alpha=x+iy$. Both are normalized operator measures and their actual Born densities, relative to $d^2\alpha/\pi$, are
--
--   $$p(\alpha\mid z)=2\exp(-2|\alpha-z|^2).$$
--
--   For the first measure, its effects are the pushforward integrals of the product coherent-state POVM. For the second, a positive diagonal-sum seed form on the invariant oscillator Schwartz space has characteristic operator $D_1(it/2)D_2(-s/2)$, identifying the specified commuting quadratures. Each attains the covariant optimum $2$. This supplies measurement identities rather than a Gaussian density defined in isolation.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2(i): two local optimal coherent-state measurements

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

/-- PDF p.6, §V.B.2(i): the two physical local measurements. The first measure is
explicitly the pushforward of the product coherent-state POVM. The characteristic
operator of the second is D_1(it/2)D_2(-s/2), fixing Q=(a+a†)/2, P=(a-a†)/(2i).
Their Gaussian laws and optimality are conclusions, not definitions of the measurements. -/
theorem wh_coherent_local :
    ∃ (avg : HilbertOperatorMeasure ℂ (MultiFock 2))
      (joint : FormSeed coherentMeasure (fun a : ℂ =>
        ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a)))),
      (joint.domain : Set (MultiFock 2)) = {v | OscillatorSchwartz v} ∧
      (∀ v w, v ∈ joint.domain → w ∈ joint.domain →
        joint.form v w = jointQuadratureForm v w) ∧
      (∀ E : Set ℂ, MeasurableSet E →
        WeakIntegral ((coherentMeasure.prod coherentMeasure).restrict
          {p : ℂ × ℂ | (p.1 + p.2) / 2 ∈ E})
          (fun p => InnerProductSpace.rankOne ℂ (displacedVacuumPair p.1 p.2) (displacedVacuumPair p.1 p.2))
          (avg.effect E) ∧
        WeakIntegral (coherentMeasure.restrict E)
          (multiOrbit (numberSeed 1 (fun _ => 0))) (avg.effect E)) ∧
      (∀ (t s : ℝ) v w, v ∈ joint.domain → w ∈ joint.domain →
        Integrable (fun a : ℂ => Complex.exp (Complex.I * (t * a.re + s * a.im : ℝ)) *
          joint.form (ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a)) v)
            (ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a)) w)) coherentMeasure ∧
        (∫ a : ℂ, Complex.exp (Complex.I * (t * a.re + s * a.im : ℝ)) *
          joint.form (ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a)) v)
            (ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a)) w) ∂coherentMeasure) =
          inner ℂ v (multiDisplacement
            (Fin.cases (Complex.I * (t : ℂ) / 2) (fun _ => -(s : ℂ) / 2)) w)) ∧
      (∀ z : ℂ, displacedVacuumPair z z ∈ joint.domain ∧
        (∀ a, formDensity joint (displacedVacuumPair z z) a = gaussianDensity 2 z a) ∧
        (∀ a, pureSeedDensity (multiOrbit (numberSeed 1 (fun _ => 0)) a) (displacedVacuumPair z z) =
          gaussianDensity 2 z a) ∧
        (∀ E : Set ℂ, MeasurableSet E →
          pureSeedDensity (avg.effect E) (displacedVacuumPair z z) =
            ∫ a in E, gaussianDensity 2 z a ∂coherentMeasure)) ∧
      (∀ B : FormSeed coherentMeasure (fun a : ℂ =>
        ContinuousLinearMap.adjoint (multiDisplacement (fun _ : Fin 2 => a))),
        multiKet (fun _ : Fin 2 => 0) ∈ B.domain →
          (B.form (multiKet (fun _ => 0)) (multiKet (fun _ => 0))).re ≤ 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
