-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P16_cellular_quotient
-- name    : QAlgorithms.Papers.Independent.Renew46.P16.cellular_quotient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:21:52.60701+00:00
-- url     : https://prove2.me/theorems/3d5314b5-beb1-46d4-b09f-c9759cc70b93
-- title:
--   Lemma 6.19 — cellular quotient by a cell order ideal
-- statement:
--   Let $R$ be a commutative integral domain and $A$ a unital cellular $R$-algebra in the weaker sense of Definition 2.1, with involution $i$, finite partially ordered shape set $\Lambda$, finite index sets $T(\lambda)$, and cellular basis $c_{s,t}^{\lambda}$. Let $\Gamma\subseteq\Lambda$ be closed toward higher cell labels: $\lambda\in\Gamma$ and $\lambda\le\mu$ imply $\mu\in\Gamma$. Put $A(\Gamma)=\operatorname{span}_R\{c_{s,t}^{\lambda}:\lambda\in\Gamma\}$. Then
--
--   $$A/A(\Gamma)\text{ is cellular with basis }\{c_{s,t}^{\lambda}+A(\Gamma):\lambda\notin\Gamma,\ s,t\in T(\lambda)\}.$$
--
--   Its involution is induced by $i$. The statement permits empty and full $\Gamma$, including the zero quotient with an empty basis. This construction passes a cellular datum to the indicated quotient.
-- source:
--   On Cellular Algebras with Jucys Murphy Elements, arXiv:0907.3459v2, PDF p. 28, Lemma 6.19

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 6.19, PDF p.28. The quotient has exactly the displayed cellular
basis and the involution induced from A. Empty and full Gamma are allowed. -/
theorem cellular_quotient {R A L : Type*} [CommRing R] [IsDomain R]
    [Ring A] [Algebra R A] [PartialOrder L] [Finite L]
    {T : L → Type*} [∀ l, Fintype (T l)]
    (c : CellIndex L T → A) (i : A →ₗ[R] A)
    (hcell : IsWeakCellularBasis (R := R) c i) (Gamma : L → Prop)
    (hGamma : ∀ l m, Gamma l → l ≤ m → Gamma m) :
    ∃ j : CellQuotient (R := R) c Gamma →ₗ[R] CellQuotient (R := R) c Gamma,
      (∀ a : A, j (cellQuotientMap (R := R) c Gamma a) = cellQuotientMap (R := R) c Gamma (i a)) ∧
      IsWeakCellularBasis (R := R) (quotientCells (R := R) c Gamma) j := by sorry

end QAlgorithms.Papers.Independent.Renew46.P16

end
