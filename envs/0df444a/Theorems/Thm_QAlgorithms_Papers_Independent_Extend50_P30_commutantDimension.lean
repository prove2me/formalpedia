-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_commutantDimension
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.commutantDimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:06:35.285287+00:00
-- url     : https://prove2.me/theorems/34857ff0-5233-46b1-aa10-f3f96d371727
-- title:
--   Dimension of the Clifford commutant
-- statement:
--   Let $d$ be prime, $t\geq1$, and $n\geq t-1$. The complex dimension of the operators commuting with every $t$-fold Clifford tensor power is given by the following product, interpreted as one when $t=1$.
--
--   $$
--   \dim_{\mathbb C}\operatorname{Comm}(\mathrm{Cliff}(n,d)^{\otimes t})=\prod_{k=0}^{t-2}(d^k+1).
--   $$
--
--   This gives the source's dimension of the clifford commutant in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 32, theorem-4.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.32, Theorem 4.9: complex dimension of the concrete commutant. -/
theorem commutantDimension (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (hn : t - 1 ≤ n) :
    Module.finrank ℂ (cliffordCommutant d n t) = commutantCount d t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
