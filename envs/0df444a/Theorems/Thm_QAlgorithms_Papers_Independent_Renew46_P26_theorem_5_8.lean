-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_5_8
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_5_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:03:04.568837+00:00
-- url     : https://prove2.me/theorems/0babf4b6-523a-4c33-89d0-3cd07f8d54a6
-- title:
--   Theorem 5.8: Young branching, content spectrum, and equivalence relations
-- statement:
--   The actual irreducible complex representation classes of $S_n$ admit compatible bijections with all $n$-box Young diagrams, under which adjacent restriction multiplicity is one exactly for a one-box Young edge and is zero otherwise. The label of a class is fixed by its actual YJM weights. With tableaux defined independently as Young-graph paths,
--
--   $$\operatorname{Spec}(n)=\operatorname{Cont}(n),\qquad \operatorname{Tab}(n)\ \cong\ \operatorname{Spec}(n),\qquad \sim\ =\ \approx.$$
--
--   The tableau-spectrum bijection is the column-minus-row content map; $\sim$ means occurrence in one irreducible and $\approx$ means admissible-swap reachability. This retains the graph, spectrum, and equivalence-relation clauses of the paper's central theorem at every level.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 22, Theorem 5.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 5.8, the paper capstone (PDF p.22; announced p.5).
Actual irreducible classes are identified at every level with all Young diagrams;
the multiplicity-one edges match the Young graph. The class labels are pinned
by their actual YJM eigenvalues, the path spectrum is identified with tableaux,
Spec=Cont, and the two independent equivalence relations coincide. -/
theorem theorem_5_8 :
    ∃ labels : ∀ n : ℕ, IrreducibleClass n ≃ {lam : YoungDiagram // lam.card = n},
      (∀ n (C : IrreducibleClass n) (D : IrreducibleClass (n + 1)),
        branchingMultiplicity C D =
          if YoungEdge (labels n C).val (labels (n + 1) D).val then 1 else 0) ∧
      (∀ n (C : IrreducibleClass n) (alpha : Fin n → ℂ),
        ClassHasWeight C alpha ↔ ∃ T : YoungTableau n,
          tableauShape T = (labels n C).val ∧ tableauContent T = alpha) ∧
      (∀ n, spectrum n = contentVectors n ∧
        (∃ e : YoungTableau n ≃ {alpha : Fin n → ℂ // alpha ∈ spectrum n},
          ∀ T, (e T).val = tableauContent T) ∧
        (∀ alpha ∈ spectrum n, ∀ beta ∈ spectrum n,
          SameIrreducible alpha beta ↔ AdmissiblyEquivalent alpha beta)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
