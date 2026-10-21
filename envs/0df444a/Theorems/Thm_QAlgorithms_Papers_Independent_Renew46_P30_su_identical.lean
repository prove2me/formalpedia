-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_su_identical
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.su_identical
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:13:55.375549+00:00
-- url     : https://prove2.me/theorems/464036e2-06ed-4e56-9982-e20ad8e10a6c
-- title:
--   §V.A.2: N identical finite-dimensional inputs
-- statement:
--   Let $d\ge1$, $N>1$, and $\psi\in\mathbb C^d$ have norm one. Under the full action $U^{\otimes N}$ of $SU(d)$ with probability Haar measure, $\psi^{\otimes N}$ lies in the symmetric subspace. Write $P_+$ for its symmetrizing projector and $W$ for its orthogonal complement. Then
--
--   $$d_S=\dim\operatorname{Sym}^N(\mathbb C^d)=\binom{d+N-1}{N},\qquad\Xi=d_S|\psi^{\otimes N}\rangle\langle\psi^{\otimes N}|+I-P_+.$$
--
--   This full-space seed is positive, normalized, stabilizer invariant, and attains the universal optimum $d_S$. When $d\ge2$, the displayed completion is not fully separable across the $N$ copies; when $d=1$, its value is $1$ and its scalar seed is separable. It does not imply any universal comparison with $Nd$.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 5, §V.A.2: N identical finite-dimensional inputs

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

/-- PDF p.5, §V.A.2: N identical copies. Printed binomial choose(d+N-1,d)
is corrected to choose(d+N-1,N), the dimension named by the source.
The printed nonseparability claim requires d>=2: at d=1 the seed is the
separable scalar identity. The optimum itself holds for every d>0. -/
theorem su_identical (d N : ℕ) (hd : 0 < d) (hN : 1 < N)
    (mu : Measure (SU d)) [mu.IsHaarMeasure] [IsProbabilityMeasure mu]
    (psi : EuclideanSpace ℂ (Fin d)) (hn : ‖psi‖ = 1) :
    ‖identicalVector d N psi‖ = 1 ∧
    Module.finrank ℂ (symmetricSpace d N) = Nat.choose (d + N - 1) N ∧
    Matrix.mulVec (symmetricProjector d N) (WithLp.ofLp (identicalVector d N psi)) =
      WithLp.ofLp (identicalVector d N psi) ∧
    MatrixMaximum mu (suTensorAction d N) (identicalVector d N psi) (identicalSeed d N psi)
      (Nat.choose (d + N - 1) N) ∧ (2 ≤ d → ¬ PositiveTensorSum d N (identicalSeed d N psi)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
