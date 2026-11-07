-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_4_1
-- name    : PlantedSubgraphLD.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:48.217515+00:00
-- url     : https://prove2.me/theorems/b92c375f-9881-48df-8a78-90581c0f601e
-- title:
--   Lemma 4.1 — $|\mathrm{Tri}(F)|=N_\Gamma(F)^2|\mathrm{Aut}(F)|$
-- statement:
--   Let $\Gamma$ be a finite simple graph. For every nonempty abstract graph $F$ with $N_\Gamma(F)>0$,
--
--   $$
--   |\mathrm{Tri}(F)|=N_\Gamma(F)^2\,|\mathrm{Aut}(F)| .
--   $$
--
--   Furthermore, for every $c$ and $n$,
--
--   $$
--   \beta_n(F)=\frac{n^{e(F)-v(F)}}{c^{e(F)}}\,|\mathrm{Tri}(F)| .
--   $$
--
--   The count of isomorphism triples is what makes $\beta_n$ comparable across the pieces of a decomposition (Lemma 4.2).
--
--   Differences from the source:
--   - generalization: the planted graph Γn (a graph on at most n vertices, n large) → any finite simple graph Γ; reason: the statement is combinatorial in Γ; the paper's Γn is a special case
--   - encoding: abstract graphs F (isomorphism classes of graphs without isolated vertices) with NΓ(F) > 0, F nonempty → elements of AbsGraph Γ, the isomorphism classes of nonempty edge subsets of Γ; e(F), v(F), |Aut(F)|, connectedness read off the representative Quotient.out F; reason: the classes of nonempty subgraphs of Γ are exactly the nonempty abstract graphs with NΓ(F) > 0, and the invariants do not depend on the representative
--   - generalization: the fixed constant c > 0 and the index n → every real c and natural n; reason: the second identity is an algebraic rewriting of the definition of βn and holds for all c, n
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 4.1, §4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_Tri
import Definitions.Def_PlantedSubgraphLD_beta

namespace PlantedSubgraphLD

/-- **Lemma 4.1.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, Lemma 4.1, p.18 (PDF p.20): "For every nonempty abstract graph
F with NΓn(F) > 0, |Tri(F)| = NΓn(F)²|Aut(F)|. Furthermore, we have
βn(F) = (n^{e(F)−v(F)}/c^{e(F)}) |Tri(F)|."

**Formalization Note** Stated for any finite simple graph `Γ` and every element `F` of
`AbsGraph Γ`; the second identity for every `c` and `n`. -/
theorem lemma_4_1 {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V) (F : AbsGraph Γ) :
    Nat.card (Tri Γ F) = count F ^ 2 * autCard F ∧
    ∀ (c : ℝ) (n : ℕ), beta c n F =
      (n : ℝ) ^ ((numEdges F : ℤ) - numVerts F) / c ^ numEdges F * (Nat.card (Tri Γ F) : ℝ) := by sorry

end PlantedSubgraphLD
