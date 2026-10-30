-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_qubitStabilizerTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.qubitStabilizerTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:56:26.312674+00:00
-- url     : https://prove2.me/theorems/f8733820-9cf1-4d84-a7dc-c39b2c1a81d6
-- title:
--   Six-copy qubit stabilizer testing
-- statement:
--   For every $n$, the fixed effect of Algorithm 1 is a valid six-copy accepting effect. Its verification unitary factors into $n$ identical fixed-size six-qubit blocks, giving the stated efficient circuit realization. For every normalized pure $n$-qubit state $\psi$, it accepts stabilizers with certainty. If every pure stabilizer $S$ satisfies $|\langle S|\psi\rangle|^2\leq1-\varepsilon^2$, then its acceptance probability obeys the bound below.
--
--   $$
--   p_{\rm accept}(S)=1,\qquad p_{\rm accept}(\psi)\leq1-\frac{\varepsilon^2}{4}.
--   $$
--
--   This gives the source's six-copy qubit stabilizer testing in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 20, theorem-3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.20, Theorem 3.3: Algorithm 1 is fixed, perfectly complete, and has the printed 1/4 constant. -/
theorem qubitStabilizerTesting (n : ℕ) :
    qubitVerificationUnitary 1 ∈ Matrix.unitaryGroup (QuditCopies 2 1 6) ℂ ∧
    qubitTest n = (2⁻¹ : ℂ) • (1 +
      (List.ofFn (fun j : Fin n => embeddedLocal j (qubitVerificationUnitary 1))).prod) ∧
    QAlgorithms.IsEffect (qubitTest n) ∧
    ∀ v : EuclideanSpace ℂ (ResidueRegister 2 n), ‖v‖ = 1 →
      (IsStabilizer v → QAlgorithms.effectProb (qubitTest n)
        (tensorPower 6 (QAlgorithms.pureDensity v)) = 1) ∧
      (∀ epsilon : ℝ, FarFromStabilizers v epsilon →
        QAlgorithms.effectProb (qubitTest n) (tensorPower 6 (QAlgorithms.pureDensity v)) ≤
          1 - epsilon ^ 2 / 4) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
