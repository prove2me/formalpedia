-- Prove2me | Theorems.Thm_TangleStructTree_Supplement_theorem_3_7
-- name    : TangleStructTree.Supplement.theorem_3_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T04:10:40.698288+00:00
-- url     : https://prove2.me/theorems/8a70ac82-21a5-47ec-a6b0-cba58a86c372
-- title:
--   Theorem 3.7 — every $\mathcal F$-tangle structure tree displays all $\mathcal F$-tangles
-- statement:
--   Let $\vec S$ be a separation system, let $\mathcal F$ be any set, and let $(T,r,\beta)$ be any $\mathcal F$-tangle structure tree of $\vec S$. Write $\beta_\ell$ for the set of labels on the path from the root to $\ell$ and $\lfloor\beta_\ell\rfloor$ for its closure.
--
--   1. For every $\mathcal F$-tangle $\tau$ of $S$ there is a unique leaf $\ell$ of $T$ such that
--   $$\lfloor\beta_\ell\rfloor=\tau .$$
--   2. If all the leaves of $T$ are forbidden, then $S$ has no $\mathcal F$-tangle.
--
--   So a single tangle structure tree lists every tangle of $S$, each exactly once, at its leaves; no finiteness, order function or condition on $\mathcal F$ is needed.
--
--   Differences from the source:
--   - encoding: a separation tree is a finite rooted tree with an edge labelling β → a SepTree: the finite prefix-closed set of root-path label lists; reason: the child labels of a node are distinct, so the label-list set determines the rooted labelled tree up to root- and label-preserving isomorphism and every finite separation tree arises
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Theorem 3.7, p.7 (PDF 18); = extended abstract Theorem 3.3, p.5

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Theorem 3.7** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I), p.7 (PDF 18); = extended abstract Theorem 3.3, p.5). Let `S⃗` be a
separation system, let `ℱ` be any set, and let `T` be any `ℱ`-tangle structure tree of `S⃗`.
(i) For every `ℱ`-tangle `τ` of `S` there is a unique leaf `ℓ` of `T` such that `⌊β_ℓ⌋ = τ`.
(ii) If all the leaves of `T` are forbidden, then `S` has no `ℱ`-tangle.

**Formalization Note** Nodes are root-path label lists (`SepTree`), `β_ℓ` is `labels ℓ` and
`⌊β_ℓ⌋` is `sepClosure (labels ℓ)`. No finiteness, order function, richness or standardness is
assumed. -/
theorem theorem_3_7 (ℱ : Set (Set E)) (T : SepTree E) (hT : T.IsTST ℱ) :
    (∀ τ : Set E, IsTangle ℱ τ → ∃! ℓ : List E, T.IsLeaf ℓ ∧ sepClosure (labels ℓ) = τ) ∧
      ((∀ ℓ : List E, T.IsLeaf ℓ → T.IsForbiddenLeaf ℱ ℓ) → ¬ ∃ τ : Set E, IsTangle ℱ τ) := by sorry

end Supplement

end TangleStructTree
