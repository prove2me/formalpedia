-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_minimalStabilizerTest
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.minimalStabilizerTest
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:22:09.731832+00:00
-- url     : https://prove2.me/theorems/9ab98a10-8aaf-4418-bffb-07d306a7b1a5
-- title:
--   Minimal perfectly complete stabilizer projector
-- statement:
--   Let $d$ be prime and $n,t\geq1$. The average of the graph unitaries over the stochastic orthogonal group is the orthogonal projector onto the complex span of all stabilizer tensor powers. This identifies a subspace, not every individual tensor-power vector in it at small $t$.
--
--   $$
--   \Pi_t^{\min}=\frac1{|O_t(d)|}\sum_{O\in O_t(d)}R(O)=P_{\operatorname{span}\{|S\rangle^{\otimes t}:S\in\mathrm{Stab}(n,d)\}}.
--   $$
--
--   This gives the source's minimal perfectly complete stabilizer projector in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 48, theorem-5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.48, Theorem 5.6: no identification of individual tensor powers is asserted for small t. -/
theorem minimalStabilizerTest (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (hn : 1 ≤ n) (ht : 1 ≤ t) :
    IsOrthogonalProjectionOnto (minimalTest d n t) (stabilizerSpan d n t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
