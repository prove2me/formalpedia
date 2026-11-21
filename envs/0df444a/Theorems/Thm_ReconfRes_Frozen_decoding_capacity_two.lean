-- Prove2me | Theorems.Thm_ReconfRes_Frozen_decoding_capacity_two
-- name    : ReconfRes.Frozen.decoding_capacity_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T21:34:52.739225+00:00
-- url     : https://prove2.me/theorems/78e51449-4871-4eeb-97a9-01e254c25c25
-- title:
--   Lemma 3.61 (decoding step) — a tight refutation of width at most W selects at least bK − 1 twins, its decoded set is independent, and its pivots are unique
-- statement:
--   For the modified frozen construction $D$ (Valid: $n \ge 2$, $1 \le K \le n-1$, $k \ge 2$, both trees with the vertices of $J$ as leaves exactly once; $b = n + 2k + 2$, $W = \beta + q + 1$), let $R$ be a tight refutation (a lean refutation of the construction's formula with the prescribed frozen axiom multiset and size at most $2\alpha - 1$) of width at most $W$. Then:
--   1. $bK \le |X(R)| + 1$, where $X(R)$ is the ancestry-selected set of test (∗): $v \in X(R)$ when some $f_v$-pivot node is an ancestor of an $a_v$-pivot node and of a $b_v$-pivot node;
--   2. the decoded set $I(R)$, the vertices of $J_0$ whose twin groups contain at least two members of $X(R)$, is independent in $J_0$;
--   3. every resolution node of $R$ has a single pivot.
--
--   These are the steps of the proof of Lemma 3.61 (decoding at capacity two) in Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.13, p. 80, which rest on the tree analysis of Lemma 3.56 (pp. 73–74). Item 1 is the inequality (†) of that proof, item 2 is the sentence "Thus $I(R)$ is independent", and item 3 is the remark of Lemma 3.56's proof that every goal-path clause is negative, so that every resolution removes the single positive literal of its branch. They are stated together as one theorem so that `ReconfRes.Frozen.lemma_3_61` reduces to it: the remaining parts of Lemma 3.61 (the bound $|X(R) \triangle X(R')| \le 2k$ across a frozen edge, $|I(R) \cap I(R')| \ge K$, and the projection of frozen paths to independent-set paths) follow by the marker argument and counting.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission 340, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/340.pdf (no DOI), §3.13, pp. 72-74 and 80, proof of Lemma 3.61 (decoding at capacity two), with the tree analysis of Lemma 3.56

import Mathlib
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction

namespace ReconfRes.Frozen
theorem decoding_capacity_two (D : ConstrData) (hD : D.Valid) (R : ProofDag (CVar D.TV))
    (hR : D.IsTight R) (hW : R.width ≤ D.W) :
    D.b * D.K ≤ (D.selected R).card + 1 ∧ IsIndepSet D.J0 (D.decoded R) ∧
    ∀ (i : Fin R.n) (x y : CVar D.TV), R.HasPivot i x → R.HasPivot i y → x = y := by sorry
end ReconfRes.Frozen
