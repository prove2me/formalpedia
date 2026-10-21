-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_ancilla_twin_beam
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.ancilla_twin_beam
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:23:08.652276+00:00
-- url     : https://prove2.me/theorems/02c23a19-b644-4963-aa18-4c1cd4866ebc
-- title:
--   §V.B.4: displacement on one half of a twin beam
-- statement:
--   Let $0\le x<1$ be real. The full two-mode twin-beam vector is the Hilbert-norm sum
--
--   $$\Psi_x=\sqrt{1-x^2}\sum_{n\ge0}x^n|n,n\rangle,\qquad\|\Psi_x\|=1.$$
--
--   For the one-sided action $D(z)\otimes I$, the closed copies $\mathcal H\otimes|n\rangle$ are orthogonal invariant equivalent irreducible subspaces whose closed span is the full Hilbert space with actual coefficient-square formal constants $b_n=1$. The diagonal-sum functional $F(\psi)=\sum_n\psi_{n,n}$ on the common invariant oscillator Schwartz core defines the generalized seed form $\overline{F(v)}F(w)$. Its covariant operator measure is normalized on full Fock space and attains, against every regular admissible covariant form on this input,
--
--   $$L_{\max}=\frac{1+x}{1-x}.$$
--
--   The value is $1$ at $x=0$ and tends to $+\infty$ as $x\to1^-$; there is no normalized endpoint state at $x=1$. This is the two-mode heterodyne measurement for the source's one-sided action.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 7, §V.B.4: displacement on one half of a twin beam

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

/-- PDF p.7, §V.B.4: one-sided displacement and generalized diagonal-sum
heterodyne POVM on the common invariant core. The multiplicity copies have
closed span equal to the full Hilbert space. The squeezing parameter is real
0<=x<1; this source has (1+x)/(1-x), without the later paper's factor 2. -/
theorem ancilla_twin_beam :
    ∃ A : FormSeed coherentMeasure (fun a : ℂ => ContinuousLinearMap.adjoint
      (multiDisplacement (Fin.cases a (fun _ => 0)))),
      (A.domain : Set (MultiFock 2)) = {v | OscillatorSchwartz v} ∧
      (∀ n : ℕ,
        let W := (Submodule.span ℂ (Set.range (fun v : Fock =>
          splitVector 1 v (multiKet (fun _ => n))))).topologicalClosure
        (∀ z v, v ∈ W → multiDisplacement (Fin.cases z (fun _ => 0)) v ∈ W) ∧
        (∀ L : Submodule ℂ (MultiFock 2), IsClosed (L : Set (MultiFock 2)) → L ≤ W →
          (∀ z v, v ∈ L → multiDisplacement (Fin.cases z (fun _ => 0)) v ∈ L) →
          L = ⊥ ∨ L = W) ∧
        Integrable (fun z : ℂ =>
          ‖inner ℂ (splitVector 1 (fockKet 0) (multiKet (fun _ => n)))
            (multiDisplacement (Fin.cases z (fun _ => 0))
              (splitVector 1 (fockKet 0) (multiKet (fun _ => n))))‖ ^ 2) coherentMeasure ∧
        (∫ z : ℂ,
          ‖inner ℂ (splitVector 1 (fockKet 0) (multiKet (fun _ => n)))
            (multiDisplacement (Fin.cases z (fun _ => 0))
              (splitVector 1 (fockKet 0) (multiKet (fun _ => n))))‖ ^ 2 ∂coherentMeasure) = 1) ∧
      (⨆ n : ℕ, (Submodule.span ℂ (Set.range (fun v : Fock =>
        splitVector 1 v (multiKet (fun _ => n))))).topologicalClosure).topologicalClosure = ⊤ ∧
      (∀ m n : ℕ, ∀ v w : Fock, m ≠ n →
        inner ℂ (splitVector 1 v (multiKet (fun _ => m)))
          (splitVector 1 w (multiKet (fun _ => n))) = 0) ∧
      (∀ m n : ℕ, ∀ z : ℂ,
        (spectatorDyad 1 (multiKet (fun _ => m)) (multiKet (fun _ => n))).comp
          (multiDisplacement (Fin.cases z (fun _ => 0))) =
        (multiDisplacement (Fin.cases z (fun _ => 0))).comp
          (spectatorDyad 1 (multiKet (fun _ => m)) (multiKet (fun _ => n)))) ∧
      (∀ v, v ∈ A.domain → Summable (fun n : ℕ => v (fun _ => n))) ∧
      (∀ v w, v ∈ A.domain → w ∈ A.domain →
        A.form v w = star (diagonalFunctional v) * diagonalFunctional w) ∧
      (∀ x : ℝ, 0 ≤ x → x < 1 →
        HasSum (fun n : ℕ => ((Real.sqrt (1 - x ^ 2) * x ^ n : ℝ) : ℂ) •
          multiKet (fun _ => n)) (twinBeam x) ∧
        ‖twinBeam x‖ = 1 ∧ twinBeam x ∈ A.domain ∧
        (A.form (twinBeam x) (twinBeam x)).re = (1 + x) / (1 - x) ∧
        (∀ B : FormSeed coherentMeasure (fun a : ℂ => ContinuousLinearMap.adjoint
          (multiDisplacement (Fin.cases a (fun _ => 0)))),
          twinBeam x ∈ B.domain → (B.form (twinBeam x) (twinBeam x)).re ≤ (1 + x) / (1 - x))) ∧
      Filter.Tendsto (fun x : ℝ => (1 + x) / (1 - x))
        (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
