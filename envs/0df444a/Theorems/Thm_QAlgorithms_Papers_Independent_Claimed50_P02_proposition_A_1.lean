-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P02_proposition_A_1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P02.proposition_A_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:36:07.808233+00:00
-- url     : https://prove2.me/theorems/2158e2b1-87bb-4797-bce7-360b70d2418f
-- title:
--   Proposition A.1: diagram trace equals physical matrix trace
-- statement:
--   Let $d\ge2$ and $p,q\ge0$. Let $z$ be any complex linear combination of walled Brauer diagrams and let $\psi^d_{p,q}$ be the physical matrix action defined by equality of labels on connected endpoints. Define the diagram trace by closing opposite endpoints and assigning $d$ to each closed loop, extended linearly. Then
--   $$
--   \operatorname{Tr}(\psi^d_{p,q}(z))=\operatorname{Tr}_{\mathrm{diag}}(z).
--   $$
--   In particular, for a single diagram $\sigma$, this common trace is $d^{\operatorname{loops}(\sigma)}$. This evaluates physical matrix traces without expanding the tensor-space matrices.
-- source:
--   Linear programming with unitary-equivariant constraints, arXiv:2207.05713v2, PDF p. 57, Proposition A.1: diagram trace equals physical matrix trace

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P02

namespace QAlgorithms.Papers.Independent.Claimed50.P02

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P69 (Sites choi)

noncomputable section

/-- Paper p.57, Proposition A.1, Eqs.(179),(180): both arbitrary complex
combinations and the single-diagram specialization. -/
theorem proposition_A_1 {d p q : ℕ} (hd : 2 ≤ d) :
    (∀ z : DiagramSum p q, Matrix.trace (diagramAction d z) = diagramTrace d z) ∧
    (∀ pi : Diagram p q,
      Matrix.trace (diagramMatrix d pi) = (d : ℂ) ^ closedLoops Finset.univ pi) := by sorry

end

end QAlgorithms.Papers.Independent.Claimed50.P02
