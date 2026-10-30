-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_cliffordOrbitDesigns
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.cliffordOrbitDesigns
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:23:34.324338+00:00
-- url     : https://prove2.me/theorems/aabddde9-25b0-4da5-82ea-c3cb34fa3b90
-- title:
--   Projective designs from finitely many Clifford orbits
-- statement:
--   Fix prime $d$ and $t\geq1$. There is an integer $M=M_{t,d}$ independent of $n$, equal to the number of permutation-transpose classes of $\Sigma_{t,t}(d)$, such that for every $n\geq t-1$ one can choose normalized fiducials $\Psi_1,\ldots,\Psi_M$ and nonnegative weights $p_i$ summing to one whose Clifford-orbit mixture is a projective $t$-design. Zero weights are allowed.
--
--   $$
--   \sum_{i=1}^M p_i\,\mathbb E_{U\in\mathrm{Cliff}(n,d)}(U\Psi_iU^\dagger)^{\otimes t}=\mathbb E_{\psi\sim\mathrm{Haar}}\psi^{\otimes t}.
--   $$
--
--   This gives the source's projective designs from finitely many clifford orbits in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 50, theorem-6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.50, Theorem 6.2: number of fiducials is fixed before n; zero weights are permitted. -/
theorem cliffordOrbitDesigns (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    ∃ M : ℕ, M = (designClasses d t).card ∧ ∀ n : ℕ, t - 1 ≤ n →
      ∃ p : Fin M → ℝ, ∃ v : Fin M → EuclideanSpace ℂ (ResidueRegister d n),
        (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, ‖v i‖ = 1) ∧
        (∑ i, (p i : ℂ) • cliffordMoment t (v i)) = haarMoment d n t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
