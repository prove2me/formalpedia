-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_relationCommutes
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.relationCommutes
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:05:10.91699+00:00
-- url     : https://prove2.me/theorems/9b1bc5e5-2dbb-4fe6-b0b6-35bb70c380c8
-- title:
--   Lagrangian operators commute with Clifford tensor powers
-- statement:
--   Let $d$ be prime and $t\geq1$. For every $n\geq0$, every stochastic Lagrangian $T\in\Sigma_{t,t}(d)$ and every Clifford unitary $U$ on $n$ qudits, the concrete relation tensor operator commutes with $U^{\otimes t}$. No stable-range condition is imposed.
--
--   $$
--   R(T)U^{\otimes t}=U^{\otimes t}R(T).
--   $$
--
--   This gives the source's lagrangian operators commute with clifford tensor powers in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 29, lemma-4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.29, Lemma 4.5: no stable-range condition is needed for membership in the commutant. -/
theorem relationCommutes (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) (T : Lagrangian d t) (U : QuditOperator d n) (hU : IsClifford U) :
    tensorRelation n T.val * tensorPower t U = tensorPower t U * tensorRelation n T.val := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
