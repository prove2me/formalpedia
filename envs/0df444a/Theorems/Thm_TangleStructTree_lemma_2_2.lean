-- Prove2me | Theorems.Thm_TangleStructTree_lemma_2_2
-- name    : TangleStructTree.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:36.622486+00:00
-- url     : https://prove2.me/theorems/2723e37e-5bfe-4c04-9579-8575406bcd51
-- title:
--   Lemma 2.2 — the closure of a consistent set without co-trivial elements is consistent
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system, and let $\tau\subseteq\vec S$ be consistent and contain no element that is co-trivial in $\vec S$. Then
--
--   1. $\lfloor\tau\rfloor$ is consistent, and
--   2. $\lfloor\tau\rfloor\setminus\tau$ contains at most one orientation of any $s\in S$.
--
--   This is what makes the closure of the label set of a path a consistent orientation once it orients all of $S$.
--
--   Differences from the source: none.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 2.2, p.5 (PDF 16)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTrivial
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsStandard
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- **Lemma 2.2** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.5 (PDF 16)). Let `τ ⊆ S⃗` be
consistent, and suppose that `τ` has no elements that are co-trivial in `S⃗`. Then `⌊τ⌋` is
consistent, and `⌊τ⌋ \ τ` contains at most one orientation of any `s ∈ S`.

**Formalization Note** `x` is co-trivial iff `x∗` is trivial. "At most one orientation of `s`":
if `x` and `x∗` both lie in `⌊τ⌋ \ τ` then `x∗ = x`. -/
theorem lemma_2_2 (τ : Set E) (hτ : IsConsistent τ) (hco : ∀ x ∈ τ, ¬ IsTrivial (rev x)) :
    IsConsistent (sepClosure τ) ∧
      ∀ x : E, x ∈ sepClosure τ \ τ → rev x ∈ sepClosure τ \ τ → rev x = x := by sorry
end TangleStructTree
