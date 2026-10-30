-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_robustHudson
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.robustHudson
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:32:06.417753+00:00
-- url     : https://prove2.me/theorems/e7760b55-037d-447d-857c-6b20b1e26c7d
-- title:
--   Robust finite-dimensional Hudson theorem
-- statement:
--   Let $d\geq2$ be odd, possibly composite, and $\psi$ any normalized pure state of $n$ qudits. Define its Wigner sum-negativity by $\mathrm{sn}(\psi)=\sum_x\max\{0,-w_\psi(x)\}$. There is a pure stabilizer state $S$ with the fidelity lower bound below. No small-negativity hypothesis is needed.
--
--   $$
--   |\langle S|\psi\rangle|^2\geq1-9d^2\mathrm{sn}(\psi).
--   $$
--
--   This gives the source's robust finite-dimensional hudson theorem in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 60, theorem-8.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.60, Theorem 8.4: robust Hudson stabilizerOverlap lower bound, for every odd d, without a smallness assumption. -/
theorem robustHudson (d n : ℕ) [NeZero d] (hd : 2 ≤ d) (hodd : Odd d)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (hv : ‖v‖ = 1) :
    ∃ S : QuditOperator d n, S ∈ stabilizers d n ∧
      1 - 9 * (d : ℝ) ^ 2 * sumNegativity v ≤ stabilizerOverlap S v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
