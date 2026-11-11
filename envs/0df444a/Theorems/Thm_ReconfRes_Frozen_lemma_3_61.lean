-- Prove2me | Theorems.Thm_ReconfRes_Frozen_lemma_3_61
-- name    : ReconfRes.Frozen.lemma_3_61
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:24:27.021419+00:00
-- url     : https://prove2.me/theorems/f0d33e7b-66e0-4ebc-aa16-f60e419dd610
-- title:
--   Lemma 3.61 — decoding at capacity two: I(R) is independent with |I(R)| ≥ K, a frozen edge changes ≤ 2k twin bits and keeps |I ∩ I′| ≥ K
-- statement:
--   For the modified construction ($b=n+2k+2$, width $W=\beta+q+1$) and every tight refutation $R$ of width at most $W$, let $X(R)$ be defined by the ancestry test (∗) and $I(R)$ consist of the original vertices whose twin groups contain at least two members of $X(R)$. Then $I(R)$ is independent in $J_0$ and $|I(R)|\ge K$. For every frozen locality-$k$ edge $R,R'$ of $G^{fr}_k(F,W,2\alpha-1)$ between such refutations,
--   $$|X(R)\,\triangle\,X(R')|\le2k,\qquad |I(R)\cap I(R')|\ge K .$$
--   Consequently every such proof path projects to an independent-set path in $J_0$ with lower bound $K$. This is the soundness half of the reduction of Theorem 3.63.
--
--   Differences from the source:
--   - encoding: the construction's vertices, heads and facts → J on Fin n × Fin b, variables of an inductive type CVar, trees as FBTree with exactly the vertices of J as leaves (every such pair of trees allowed); reason: the paper chooses arbitrary trees; the statement quantifies over all of them
--   - encoding: "every such proof path" → every path in G^fr_k(F, W, 2α − 1) (up to renaming) starting at a tight refutation of width at most W, projected by I; reason: the vertices of that graph reachable from a tight refutation are tight (Proposition 3.3) and have width at most W
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 80–81, Lemma 3.61

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Lemma 3.61** (decoding at capacity two). For the modified construction (`b = n + 2k + 2`,
`W = β + q + 1`, any two leaf-exact full binary trees), every tight refutation `R` of width at most
`W` has `I(R)` independent in `J₀` with `|I(R)| ≥ K`; every frozen locality-`k` edge `R, R'` of
`G^fr_k(F, W, 2α − 1)` between tight refutations has `|X(R) △ X(R')| ≤ 2k` and
`|I(R) ∩ I(R')| ≥ K`; consequently every frozen path from a tight refutation of width at most `W`
projects to an independent-set path in `J₀` with lower bound `K`. -/
theorem lemma_3_61 (D : ConstrData) (hD : D.Valid) :
    (∀ R : ProofDag (CVar D.TV), D.IsTight R → R.width ≤ D.W →
      IsIndepSet D.J0 (D.decoded R) ∧ D.K ≤ (D.decoded R).card) ∧
    (∀ R R' : ProofDag (CVar D.TV), D.IsTight R → D.IsTight R' →
      FrozenAdj D.k D.formula D.W (2 * D.α - 1) R R' →
      (symmDiff (D.selected R) (D.selected R')).card ≤ 2 * D.k ∧
      D.K ≤ (D.decoded R ∩ D.decoded R').card) ∧
    (∀ R R' : ProofDag (CVar D.TV), D.IsTight R → R.width ≤ D.W →
      FrozenConnected D.k D.formula D.W (2 * D.α - 1) R R' →
      ISConnected D.J0 D.K (D.decoded R) (D.decoded R')) := by sorry

end ReconfRes.Frozen
