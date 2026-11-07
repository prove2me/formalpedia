-- Prove2me | Theorems.Thm_TangleStructTree_lemma_2_1
-- name    : TangleStructTree.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:23.195439+00:00
-- url     : https://prove2.me/theorems/3b8f8754-0ce6-475e-95b7-ef2720f98e3a
-- title:
--   Lemma 2.1 — closure is monotone and fixes consistent orientations
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system and let $\sigma\subseteq\tau\subseteq\vec S$ be consistent sets. Then
--   $$
--   \lfloor\sigma\rfloor\subseteq\lfloor\tau\rfloor .
--   $$
--   If moreover $\tau$ is an orientation of all of $S$, then $\lfloor\tau\rfloor=\tau$.
--
--   The lemma lets the closures along a root–leaf path of a separation tree grow monotonically, and identifies a consistent orientation with its closure.
--
--   Differences from the source: none.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), Lemma 2.1, p.5 (PDF 16)

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

/-- **Lemma 2.1** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.5 (PDF 16)). Let `σ ⊆ τ ⊆ S⃗`
be consistent sets. Then `⌊σ⌋ ⊆ ⌊τ⌋`. If `τ` is an orientation of all of `S`, then `⌊τ⌋ = τ`. -/
theorem lemma_2_1 (σ τ : Set E) (hστ : σ ⊆ τ) (hσ : IsConsistent σ) (hτ : IsConsistent τ) :
    sepClosure σ ⊆ sepClosure τ ∧ (IsOrientation τ → sepClosure τ = τ) := by sorry
end TangleStructTree
