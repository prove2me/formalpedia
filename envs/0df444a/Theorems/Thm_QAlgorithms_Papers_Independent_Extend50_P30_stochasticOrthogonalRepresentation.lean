-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_stochasticOrthogonalRepresentation
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.stochasticOrthogonalRepresentation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:08:24.611226+00:00
-- url     : https://prove2.me/theorems/93c7fb51-d0ac-4c38-be22-f5a28af2ebb9
-- title:
--   Unitary graph representation
-- statement:
--   Let $d$ be prime, $t\geq1$, and $n\geq0$. A stochastic quadratic isometry $O\in O_t(d)$ has graph $T_O=\{(Ox,x):x\in\mathbb F_d^t\}\in\Sigma_{t,t}(d)$. Its incidence operator and its $n$-fold tensor operator are unitary. These operators preserve identity and multiplication, hence form a unitary representation of $O_t(d)$. For $n\geq1$, every $T$ whose $R(T)$ is invertible is such a graph.
--
--   $$
--   r(T_O)=\sum_x|Ox\rangle\langle x|,\qquad R(O)R(P)=R(OP),\quad R(I)=I.
--   $$
--
--   This gives the source's unitary graph representation in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 35, lemma-4.13

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.35, Lemma 4.13: graph operators are unitary and give a representation.
The invertibility converse needs n>=1; all other clauses include n=0. -/
theorem stochasticOrthogonalRepresentation (d n t : ℕ) [NeZero d] [Fact (Nat.Prime d)]
    (ht : 1 ≤ t) :
    (∀ O : StochasticOrthogonal d t,
      IsStochasticLagrangian (graphRelation O.val) ∧
      relationOperator (graphRelation O.val) ∈ Matrix.unitaryGroup (ResidueRegister d t) ℂ ∧
      tensorRelation n (graphRelation O.val) ∈ Matrix.unitaryGroup (QuditCopies d n t) ℂ) ∧
    (1 ≤ n → ∀ T : Lagrangian d t, IsUnit (tensorRelation n T.val) →
      ∃ O : StochasticOrthogonal d t, T.val = graphRelation O.val) ∧
    tensorRelation n (graphRelation (1 : Matrix (Fin t) (Fin t) (ZMod d))) = 1 ∧
    (∀ O : StochasticOrthogonal d t, IsStochasticOrthogonal O.val.transpose) ∧
    (∀ O P : StochasticOrthogonal d t,
      IsStochasticOrthogonal (O.val * P.val) ∧
      tensorRelation n (graphRelation O.val) * tensorRelation n (graphRelation P.val) =
        tensorRelation n (graphRelation (O.val * P.val))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
