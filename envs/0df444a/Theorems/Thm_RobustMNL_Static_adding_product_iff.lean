-- Prove2me | Theorems.Thm_RobustMNL_Static_adding_product_iff
-- name    : RobustMNL.Static.adding_product_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:27.2988+00:00
-- url     : https://prove2.me/theorems/2bba46ee-7d25-4c70-88cc-82330c1eb630
-- title:
--   Lemma 3.1 — for i ∉ A: rᵢ > f(A, v) ⟺ f(A ∪ {i}, v) > f(A, v) ⟺ rᵢ > f(A ∪ {i}, v)
-- statement:
--   **When is adding a product beneficial?** Let $v \in \mathbb R^{n+1}_{++}$, let $A \subseteq \mathcal A$ be an assortment and let $i \notin A$. Then the following three statements are equivalent:
--
--   1. $r_i > f(A, v)$;
--   2. $f(A \cup \{i\}, v) > f(A, v)$;
--   3. $r_i > f(A \cup \{i\}, v)$.
--
--   In words: adding product $i$ strictly increases the expected revenue exactly when its revenue exceeds the current expected revenue, and then it also exceeds the new one. Lemma 3.1 drives the exchange arguments behind the structural results of the paper (Theorems 3.2 and 3.6).
--
--   **Formalization Note** The equivalence is stated as `List.TFAE` of the three statements. Products are `Fin n` (Lean index $i$ is the paper's product $i+1$); revenues are arbitrary reals.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Lemma 3.1, p. 6

import Mathlib
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Static

theorem adding_product_iff {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) (hp : IsPos p)
    (A : Finset (Fin n)) (i : Fin n) (hi : i ∉ A) :
    List.TFAE [r i > rev r A p, rev r (insert i A) p > rev r A p,
      r i > rev r (insert i A) p] := by sorry

end RobustMNL.Static
