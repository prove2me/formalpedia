-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_relationPartialIsometry
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.relationPartialIsometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:14:58.1812+00:00
-- url     : https://prove2.me/theorems/63418215-4757-4fdb-a160-0d95d65de845
-- title:
--   Coset expansion and rank of a relation operator
-- statement:
--   Let $d$ be prime, $t\geq1$, and let $T$ have left defect $N$, right defect $M$, and its canonically induced map $T_J:M^\perp/M\to N^\perp/N$. The ket $|N,[x]\rangle$ is the normalized uniform superposition on $x+N$. The normalized relation operator is a partial isometry, with rank equal to either defect-quotient cardinality.
--
--   $$
--   \frac{r(T)}{|N|}=\sum_{[y]\in M^\perp/M}|N,T_J[y]\rangle\langle M,[y]|,\qquad\operatorname{rank}r(T)=|N^\perp/N|=|M^\perp/M|.
--   $$
--
--   This gives the source's coset expansion and rank of a relation operator in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 39, lemma-4.23

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.39, Lemma 4.23: r(T)/|left defect| is a partial isometry; rank is the quotient cardinality.
The quotient direction corrects the reversed type in the introductory sentence of the lemma. -/
theorem relationPartialIsometry (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (T : Lagrangian d t) :
    let B := (Nat.card (leftDefect T.val) : ℂ)⁻¹ • relationOperator T.val
    B = ∑ q : defectQuotient (rightDefect T.val),
      ketBra (cosetState (leftDefect T.val) (canonicalDefectMap T.val q))
        (cosetState (rightDefect T.val) q) ∧
    B * Bᴴ * B = B ∧
    Matrix.rank (relationOperator T.val) = Nat.card (defectQuotient (leftDefect T.val)) ∧
    Matrix.rank (relationOperator T.val) = Nat.card (defectQuotient (rightDefect T.val)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
