-- Prove2me | Theorems.Thm_SteinerCutDominants_lemma_6
-- name    : SteinerCutDominants.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:45.045745+00:00
-- url     : https://prove2.me/theorems/1cf8a889-ad2f-4cdd-a082-d5714c1677f4
-- title:
--   Lemma 6: size bounds for irreducible Steiner graphs
-- statement:
--   Every irreducible facet inducing Steiner graph $(G,T)$ with $|T|\ge 3$ has
--   $$
--   |E(G)|\le|V(G)|+|T|-3\qquad\text{and}\qquad|V(G)|\le 3|T|-6 .
--   $$
--   If equality holds in any of those two inequalities, then, for every choice of facet weights, $\delta(t)$ is a root for every $t\in T$.
--
--   The first bound also holds for $|T|=2$, where it forces $G$ to be a tree, hence the single edge $K_2$. Theorem 4 follows.
--
--   Differences from the source:
--   - generalization: |E(G)| ≤ |V(G)| + |T| − 3 for |T| ≥ 3 → the same bound for all |T| ≥ 2; reason: the page's proof does not use |T| ≥ 3 for this bound; it specializes to the source, and it replaces the page's appeal to max-flow min-cut at |T| = 2
--   - encoding: bounds with subtraction → |E| + 3 ≤ |V| + |T|, |V| + 6 ≤ 3|T|; reason: no natural-number subtraction
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Lemma 6, p.11

import Mathlib
import Definitions.Def_SteinerCutDominants_IsIrreducible
import Definitions.Def_SteinerCutDominants_IsRoot

namespace SteinerCutDominants

/-- **Lemma 6** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.11). Every
irreducible facet inducing Steiner graph `(G, T)` with `|T| ≥ 3` has `|E(G)| ≤ |V(G)| + |T| - 3` and
`|V(G)| ≤ 3|T| - 6`; if equality holds in either, then, for every choice of facet weights, `δ(t)` is
a root for every `t ∈ T`.

**Formalization Note** The constants are moved across, so no natural-number subtraction occurs. The
first bound is stated for all `|T| ≥ 2`, a generalization the page's proof gives without change. "For
every choice of facet weights" is the quantification over `H`, which carries `c`. -/
theorem lemma_6 (H : WSG) (hH : IsIrreducible H) :
    Fintype.card H.G.edgeSet + 3 ≤ Fintype.card H.V + H.T.card ∧
      (3 ≤ H.T.card →
        Fintype.card H.V + 6 ≤ 3 * H.T.card ∧
          ((Fintype.card H.G.edgeSet + 3 = Fintype.card H.V + H.T.card ∨
              Fintype.card H.V + 6 = 3 * H.T.card) →
            ∀ t ∈ H.T, IsRoot H {t})) := by sorry

end SteinerCutDominants
