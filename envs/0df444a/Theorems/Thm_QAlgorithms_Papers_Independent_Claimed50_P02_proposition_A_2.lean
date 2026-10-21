-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_proposition_A_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.proposition_A_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:36:58.130473+00:00
-- url     : https://prove2.me/theorems/9a9fc78d-5a85-4243-b935-90f8e11df928
-- title:
--   Proposition A.2: diagram partial trace intertwines matrix action
-- statement:
--   Let $d\ge2$, $p,q\ge0$, and let $S$ be any subset of the $p+q$ register positions. Keep the untraced registers in their original order. For every complex linear combination $z$ of walled diagrams,
--   $$
--   \operatorname{Tr}_S\bigl(\psi^d_{p,q}(z)\bigr)
--   =\psi^d_{p',q'}\bigl(\operatorname{Tr}^{\mathrm{diag}}_S(z)\bigr).
--   $$
--   Here $p',q'$ count the remaining primal and dual registers. For a single diagram $\sigma$, the right side equals $d^{\operatorname{loops}_S(\sigma)}\psi^d_{p',q'}(\sigma^S)$: connect opposite endpoints in $S$, erase closed components and retain the matching on the remaining endpoints. This identity requires no injectivity or large-$d$ assumption.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 57, Proposition A.2: diagram partial trace intertwines matrix action

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper pp.57–58, Proposition A.2, Eqs.(185),(186): diagrammatic contraction
intertwines the physical partial trace, with no faithfulness restriction on d. -/
theorem proposition_A_2 {d p q : ℕ} (hd : 2 ≤ d) (S : Finset (Fin (p+q))) :
    (∀ z : DiagramSum p q,
      matrixPartialTrace S (diagramAction d z) = relationAction d (diagramPartialTrace d S z)) ∧
    (∀ pi : Diagram p q, matrixPartialTrace S (diagramMatrix d pi) =
      ((d : ℂ) ^ closedLoops S pi) • relationMatrix d (contractedRelation S pi)) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
