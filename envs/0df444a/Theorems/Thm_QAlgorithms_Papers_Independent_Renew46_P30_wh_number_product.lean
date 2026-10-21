-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P30_wh_number_product
-- name    : QAlgorithms.Papers.Independent.Renew46.P30.wh_number_product
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:16:43.933193+00:00
-- url     : https://prove2.me/theorems/04dc283f-d0a5-4efc-83a2-5249c459917e
-- title:
--   §V.B.2: product number-state decomposition and likelihood
-- statement:
--   Let $N=r+1>1$ and let the input be a product number vector $|i_1,\ldots,i_N\rangle$ of total occupation $K$. Use the actual concentration unitary $V$. For each first-mode occupation $n$, take the remaining-mode coefficient vector of $V|i_1,\ldots,i_N\rangle$, its norm $C_n$, and its unit normalization $\Phi_n$ when $C_n>0$. The occupied $\Phi_n$ are orthonormal; $C_n=0$ for $n>K$, and
--
--   $$|i_1,\ldots,i_N\rangle=\sum_{n=0}^K C_n V^\dagger(|n\rangle\otimes\Phi_n),\qquad L_{\max}=N\left(\sum_{n=0}^K C_n\right)^2.$$
--
--   An explicit positive bounded seed consists of the canonical rank-one term and the vacuum-tensor identity on the orthogonal complement of the occupied spectator vectors, conjugated by $V$. It defines a full normalized operator measure and attains the bound, including against regular generalized covariant seed forms. This construction is for number products, not arbitrary product superpositions.
-- source:
--   Covariant quantum measurements which maximize the likelihood, arXiv:quant-ph/0403083v1, PDF p. 6, §V.B.2: product number-state decomposition and likelihood

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

/-- PDF p.6, §V.B.2: number-product decomposition, occupied multiplicity orthonormality,
full normalized completion and the attained N(sum C_n)^2 maximum. -/
theorem wh_number_product (r : ℕ) (hr : 0 < r) (input : Fin (r + 1) → ℕ) :
    (∀ n, photonTotal input < n → numberCoefficient r input n = 0) ∧
    (∀ n, 0 < numberCoefficient r input n → ‖numberPhi r input n‖ = 1) ∧
    (∀ n m, n ≠ m → 0 < numberCoefficient r input n → 0 < numberCoefficient r input m →
      inner ℂ (numberPhi r input n) (numberPhi r input m) = 0) ∧
    multiKet input =
      ∑ n ∈ Finset.range (photonTotal input + 1), (numberCoefficient r input n : ℂ) •
        ContinuousLinearMap.adjoint (fockConcentration r)
          (splitVector r (fockKet n) (numberPhi r input n)) ∧
    MultiMaximum (multiKet input) (numberSeed r input)
      ((r + 1 : ℕ) * (∑ n ∈ Finset.range (photonTotal input + 1), numberCoefficient r input n) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P30

end
