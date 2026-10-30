-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_sixCopyOptimality
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.sixCopyOptimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:23:00.62537+00:00
-- url     : https://prove2.me/theorems/5c79179c-951d-4e2d-9947-255b0d60ff5a
-- title:
--   Six copies are necessary for dimension-independent qubit testing
-- statement:
--   For $t=4,5$, the uniform stabilizer and Haar pure-state moments on $n$ qubits become indistinguishable as $n\to\infty$. Consequently, no family of effects on any fixed $t\leq5$ copies can be perfectly complete for all stabilizers and have a dimension-independent positive rejection probability on all states with stabilizer fidelity at most $3/4$. This remains impossible after discarding any finite initial set of register sizes. Quantification is over all effects, including collective measurements.
--
--   $$
--   \lim_{n\to\infty}\frac12\|\mathbb E_SS^{\otimes t}-\mathbb E_\psi\psi^{\otimes t}\|_1=0\quad(t=4,5).
--   $$
--
--   This gives the source's six copies are necessary for dimension-independent qubit testing in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 49, six-copy-optimality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.49: indistinguishability is against every accepting effect, not just Algorithm 1. -/
theorem sixCopyOptimality :
    (∀ t : ℕ, t = 4 ∨ t = 5 → Filter.Tendsto
      (fun n => QAlgorithms.traceNorm (stabilizerMoment 2 n t - haarMoment 2 n t) / 2)
      Filter.atTop (nhds 0)) ∧
    (∀ t : ℕ, t ≤ 5 → ∀ n0 : ℕ, ¬ ∃ eta : ℝ, 0 < eta ∧
      ∃ A : (n : ℕ) → Matrix (QuditCopies 2 n t) (QuditCopies 2 n t) ℂ,
        (∀ n, QAlgorithms.IsEffect (A n)) ∧
        (∀ n, n0 ≤ n → ∀ v : EuclideanSpace ℂ (ResidueRegister 2 n), IsStabilizer v →
          QAlgorithms.effectProb (A n) (tensorPower t (QAlgorithms.pureDensity v)) = 1) ∧
        (∀ n, n0 ≤ n → ∀ v : EuclideanSpace ℂ (ResidueRegister 2 n), ‖v‖ = 1 → FarFromStabilizers v (1 / 2) →
          QAlgorithms.effectProb (A n) (tensorPower t (QAlgorithms.pureDensity v)) ≤ 1 - eta)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
