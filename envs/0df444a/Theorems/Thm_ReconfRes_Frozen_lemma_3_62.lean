-- Prove2me | Theorems.Thm_ReconfRes_Frozen_lemma_3_62
-- name    : ReconfRes.Frozen.lemma_3_62
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:24:38.209181+00:00
-- url     : https://prove2.me/theorems/e40639cf-6c2e-4f9b-918b-d40d4b712989
-- title:
--   Lemma 3.62 — canonical proofs of independent sets differing in one vertex are joined by locality-two frozen moves at width W and size 2α − 1, with consistent indices
-- statement:
--   For the modified construction, let $X,Y\subseteq V(J)$ be independent sets of size at least $\ell$ differing in one vertex. Then the fixed canonical proofs $R_X$ and $R_Y$ (Lemma 3.58, with source occurrences indexed, the two $f_v$ units being $P_v$ and $Q_v$) are connected by frozen moves of locality at most two, at width $W$ and size $2\alpha-1$:
--   $$(R_X,\mathrm{pos}_X)\ \leftrightsquigarrow\ (R_Y,\mathrm{pos}_Y)\quad\text{in } G^{fr}_2(F,W,2\alpha-1),$$
--   and these paths retain consistent indices for every source occurrence. This is the completeness half of the reduction of Theorem 3.63, and the consistent indices are what Lemma 3.60 needs to lift the paths.
--
--   **Formalization Note.** A canonical proof is any refutation that presents the comb of the recipe of Lemma 3.58, for fixed orders of the tree internals and of the final deletions (shared by $X$ and $Y$) and for orders of the private $T$ deletions, unselected pairs, selected packets and prepared $b$ heads chosen separately for each set.
--
--   Differences from the source:
--   - encoding: the construction's vertices, heads and facts → J on Fin n × Fin b, variables of an inductive type CVar, trees as FBTree with exactly the vertices of J as leaves (every such pair of trees allowed); reason: the paper chooses arbitrary trees; the statement quantifies over all of them
--   - generalization: "any two fixed canonical proofs" (orders fixed once) → for every choice of the per-set orders (private T deletions, unselected pairs, selected packets, prepared b heads) of X and of Y, separately; reason: the paper allows these orders to be chosen arbitrarily (pp. 76, 82) and its proof sorts them; a fixed choice is one instance
--   - encoding: consistent indices of the source occurrences → IndexedFrozenConnected over the index set srcs, each step a move or isomorphism carrying pos to pos′; reason: the paper's definition of consistent indexing (p. 78)
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), pp. 81–82, Lemma 3.62 (canonical proofs: Lemma 3.58, pp. 75–76)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph
import Definitions.Def_ReconfRes_Frozen_VertexCover
import Definitions.Def_ReconfRes_Frozen_Construction

open MultiplierAssoc206.Resolution

namespace ReconfRes.Frozen

/-- **Lemma 3.62** (canonical paths at locality two). For the modified construction, let `X`, `Y`
be independent sets of `J` of size at least `ℓ` differing in one vertex. Then any canonical proof
of `X` and any canonical proof of `Y` (built with the same fixed tree-internal and final-deletion
orders; any orders of the private `T` deletions, unselected pairs, selected packets and prepared
`b` heads), with their source occurrences indexed as in the recipe (`P_v`, `Q_v` the two `f_v`
units), are joined by a path of frozen moves of locality at most two in `G^fr_2(F, W, 2α − 1)`
that keeps the index of every source occurrence. -/
theorem lemma_3_62 (D : ConstrData) (hD : D.Valid) (O : D.CanonOrders) (hO : O.Valid)
    (X Y : Finset D.TV) (hX : IsIndepSet D.J X) (hY : IsIndepSet D.J Y)
    (hXℓ : D.ℓ ≤ X.card) (hYℓ : D.ℓ ≤ Y.card)
    (hXY : (∃ v, v ∉ X ∧ Y = insert v X) ∨ (∃ v, v ∉ Y ∧ X = insert v Y))
    (LX LY : D.SetOrders) (RX RY : ProofDag (CVar D.TV))
    (posX : Src D.TV → Fin RX.n) (posY : Src D.TV → Fin RY.n)
    (hRX : D.IsCanonical O X LX RX posX) (hRY : D.IsCanonical O Y LY RY posY) :
    IndexedFrozenConnected 2 D.formula D.W (2 * D.α - 1) D.inv D.srcs ⟨RX, posX⟩ ⟨RY, posY⟩ := by sorry

end ReconfRes.Frozen
