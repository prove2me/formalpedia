-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_oneShotMother
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.oneShotMother
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:10:47.19498+00:00
-- url     : https://prove2.me/theorems/0179cb6c-6f0d-480f-95b5-f96c33d1a725
-- title:
--   One-shot fully quantum Slepian–Wolf bound
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\psi^{RAB}$ be pure, and identify $A=A_1\otimes A_2$ with $d_A=d_{A_1}d_{A_2}$ and both factors positive. There are a unitary encoder $U$ on $A$ and an isometric decoder $V:A_1B\to\widehat B\widetilde B$, where $\widehat B$ is a full copy of $AB$ and $\widetilde B$ is a copy of $A_2$, satisfying
--
--   $$
--   \left\|(I_R\otimes VU)\psi(I_R\otimes VU)^\dagger-\psi^{R\widehat B}\otimes\Phi^{A_2\widetilde B}\right\|_1
--   \le 2\left[\frac{2d_A d_R}{d_{A_1}^2}\left(\operatorname{Tr}[(\psi^{AR})^2]+2\operatorname{Tr}[(\psi^A)^2]\operatorname{Tr}[(\psi^R)^2]\right)\right]^{1/4}.
--   $$
--
--   Alice retains $A_2$, sends $A_1$, and Bob alone applies $V$. The full copied source makes the identifying isometry $W$ the identity. Communication and distilled entanglement have dimensions $d_{A_1}$ and $d_{A_2}$ respectively.
--
--   The bound simultaneously preserves the reference correlation and produces an independent EPR state.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 6, Theorem IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem IV.1, PDF p.6 (proof p.9): joint one-shot FQSW in the full trace norm. -/
theorem oneShotMother {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (a1 a2 : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (psi : EuclideanSpace ℂ (R × (Fin (a1*a2) × B))) (hpsi : IsState psi) :
    ∃ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
    ∃ V : Matrix ((Fin (a1*a2) × B) × Fin a2) (Fin a1 × B) ℂ,
      IsIso V ∧
      traceNorm (idTensorSuperop (conjSuperop (motherIsometry (U : Matrix _ _ ℂ) V))
        (pureDensity psi) - oneShotTarget a1 a2 (pureDensity psi)) ≤
      2 * Real.rpow
        ((2 * (a1*a2 : ℕ) * (Fintype.card R : ℝ) / (a1 : ℝ)^2) *
          (purity (marginalRA (pureDensity psi)) +
            2 * purity (traceLeft (marginalRA (pureDensity psi))) *
              purity (traceRight (marginalRA (pureDensity psi))))) (1/4 : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
