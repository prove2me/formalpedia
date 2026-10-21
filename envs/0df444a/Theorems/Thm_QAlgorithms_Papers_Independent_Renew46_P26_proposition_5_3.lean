-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_proposition_5_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.proposition_5_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:00:00.595123+00:00
-- url     : https://prove2.me/theorems/55ef1427-e2e3-4e21-b261-3a4cc9b0560f
-- title:
--   Proposition 5.3
-- statement:
--   Let $\operatorname{Tab}(n)$ be paths of $n$ one-box additions from the empty Young diagram. For a tableau $T$, let $c(T)$ list the column-minus-row contents of its successively added boxes. Then
--
--   $$c:\operatorname{Tab}(n)\longrightarrow\operatorname{Cont}(n)\text{ is bijective},\qquad c(T)\approx c(U)\iff\operatorname{shape}(T)=\operatorname{shape}(U).$$
--
--   Here $\approx$ is defined independently as finite reachability by admissible adjacent swaps, whose entries do not differ by $\pm1$. This identifies combinatorial paths with independently specified integer sequences.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 20, Proposition 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Proposition 5.3 (PDF p.20), including bijectivity and exactly the endpoint
criterion for the independent finite admissible-swap relation. -/
theorem proposition_5_3 (n : ℕ) :
    Function.Injective (tableauContent (n := n)) ∧
    Set.range (tableauContent (n := n)) = contentVectors n ∧
    (∀ T U : YoungTableau n, AdmissiblyEquivalent (tableauContent T) (tableauContent U) ↔
      tableauShape T = tableauShape U) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
