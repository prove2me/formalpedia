-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_cliffordMother
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.cliffordMother
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:19:47.311601+00:00
-- url     : https://prove2.me/theorems/580be6d3-e918-49f8-9de7-826fa2ef6537
-- title:
--   Uniform Clifford replacement and unchanged one-shot FQSW bound
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $A=A_1A_2$ be qubit factors with $m_1,m_2\ge0$ qubits and let $\psi^{RAB}$ be any normalized pure state. The Clifford normalizer modulo scalar phases is finite. For every two-copy operator $X$, its uniform Clifford average equals the normalized Haar average:
--
--   $$
--   \frac1{|G|}\sum_{g\in G}(g\otimes g)X(g\otimes g)^\dagger
--   =\int(U\otimes U)X(U\otimes U)^\dagger\,dU.
--   $$
--
--   Consequently there exist a Clifford encoder $g$ and a physical isometric Bob decoder for which the complete one-shot mother product target obeys exactly the IV.1 error bound, with $d_{A_i}=2^{m_i}$. No stabilizer assumption on the source is made.
--
--   The average identity is cited background [29]; its use to retain the FQSW guarantee is this paper's application. Mathematical existence makes no efficient-search claim.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 19, Section XI, Eq. (53) and application

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section XI, PDF p.19: the one-shot FQSW guarantee is achievable using a
uniform Clifford randomization has the same two-copy average as Haar [29],
and a Clifford encoder achieves exactly the one-shot bound. Finiteness is a
conclusion rather than an unproved typeclass assumption. The source need not be
stabilizer. No efficient search or certification algorithm is asserted. -/
theorem cliffordMother {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (m1 m2 : ℕ)
    (psi : EuclideanSpace ℂ (R × (Fin (2^m1*2^m2) × B))) (hpsi : IsState psi) :
    ∃ enumeration : Fintype (Clifford.ProjectiveGroup (m1+m2)),
    letI := enumeration
    (∀ M : Matrix (Fin (2^m1*2^m2) × Fin (2^m1*2^m2))
        (Fin (2^m1*2^m2) × Fin (2^m1*2^m2)) ℂ,
      (∫ U : Matrix.unitaryGroup (Fin (2^m1*2^m2)) ℂ,
        twoCopy (U : Matrix _ _ ℂ) M ∂(Schur.unitaryHaar (2^m1*2^m2))) =
      ((Fintype.card (Clifford.ProjectiveGroup (m1+m2)) : ℂ)⁻¹) •
        ∑ g : Clifford.ProjectiveGroup (m1+m2), twoCopy (cliffordOnFactors m1 m2 g) M) ∧
    ∃ g : Clifford.ProjectiveGroup (m1+m2),
    ∃ V : Matrix ((Fin (2^m1*2^m2) × B) × Fin (2^m2)) (Fin (2^m1) × B) ℂ,
      IsIso V ∧
      traceNorm (idTensorSuperop (conjSuperop (motherIsometry (cliffordOnFactors m1 m2 g) V))
        (pureDensity psi) - oneShotTarget (2^m1) (2^m2) (pureDensity psi)) ≤
      2 * Real.rpow
        ((2 * ((2^m1*2^m2 : ℕ) : ℝ) * (Fintype.card R : ℝ) / ((2^m1 : ℕ) : ℝ)^2) *
          (purity (marginalRA (pureDensity psi)) +
            2 * purity (traceLeft (marginalRA (pureDensity psi))) *
              purity (traceRight (marginalRA (pureDensity psi))))) (1/4 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
