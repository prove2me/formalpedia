-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_realFourCopyTesting
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.realFourCopyTesting
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:58:31.45978+00:00
-- url     : https://prove2.me/theorems/faa86f42-2789-4fae-97e4-9166828ab676
-- title:
--   Four-copy testing for real states
-- statement:
--   For a normalized $n$-qubit state with real computational-basis amplitudes, a single Bell measurement on two copies samples directly from $p_\psi$. Following it with the two-copy Weyl verification gives the fixed four-copy test. It is perfectly complete and has the same $1/4$ soundness guarantee as Theorem 3.3.
--
--   $$
--   \Pr[\text{Bell outcome }a]=p_\psi(a),\qquad p_{\rm accept}\leq1-\varepsilon^2/4.
--   $$
--
--   This gives the source's four-copy testing for real states in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 22, remark-3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Remark 3.5. The printed reference to Theorem 3.2 means the testing guarantees of 3.3. -/
theorem realFourCopyTesting (n : ℕ) :
    QAlgorithms.IsEffect (realQubitTest n) ∧
    ∀ v : EuclideanSpace ℂ (ResidueRegister 2 n), ‖v‖ = 1 → (∀ x, (v x).im = 0) →
      (∀ a : DiscretePhaseSpace 2 n, QAlgorithms.effectProb (QAlgorithms.pureDensity (weylBellVector n a))
        (Matrix.kronecker (QAlgorithms.pureDensity v) (QAlgorithms.pureDensity v)) = characteristicDistribution v a) ∧
      (IsStabilizer v → QAlgorithms.effectProb (realQubitTest n)
        (tensorPower 4 (QAlgorithms.pureDensity v)) = 1) ∧
      (∀ epsilon : ℝ, FarFromStabilizers v epsilon →
        QAlgorithms.effectProb (realQubitTest n) (tensorPower 4 (QAlgorithms.pureDensity v)) ≤
          1 - epsilon ^ 2 / 4) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
