-- Prove2me | Theorems.Thm_TangleStructTree_efficient_strongly_of_injective
-- name    : TangleStructTree.efficient_strongly_of_injective
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:38.514205+00:00
-- url     : https://prove2.me/theorems/e453ff67-9abd-40c1-89a3-9cf589b7094a
-- title:
--   §4 note — for injective order functions, efficient subsets of partial orientations are strongly efficient
-- statement:
--   Let $\vec S$ be an ordered separation system whose order function is injective on $S$, and let $\tau$ be a partial orientation of $S$. Then every subset $\sigma\subseteq\tau$ that is efficient in $\tau$ is strongly efficient in $\tau$.
--
--   The partial-orientation hypothesis is needed: $\vec s$ weakly eclipses $\overleftarrow{s}$ if $\vec s<\overleftarrow{s}$ (paper's footnote 10). The note closes the gap between the efficiency given by Lemma 4.2(ii) and the strong efficiency demanded by richness.
--
--   Differences from the source:
--   - encoding: an order function S → ℝ extended to S⃗ by |s⃗| = |s⃖| = |s| → ord : E → ℝ with ord (x∗) = ord x (IsOrderFunction); reason: such maps are exactly the extensions of maps S → ℝ; same instances
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19), unnumbered note before Lemma 4.2, with footnote 10

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

/-- **Injective order functions** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version,
§4, p.8 (PDF 19)): if the order function on `S` is injective and `τ` is a partial orientation of `S`,
then every efficient subset of `τ` is strongly efficient in `τ`. (Footnote 10: the assumption on `τ`
is needed, since `s⃗` eclipses `s⃖` weakly if `s⃗ < s⃖`.) -/
theorem efficient_strongly_of_injective (ord : E → ℝ) (hord : IsOrderFunction ord)
    (hinj : OrderInjective ord) (τ σ : Set E) (hτ : IsPartialOrientation τ)
    (hσ : Efficient ord σ τ) :
    StronglyEfficient ord σ τ := by sorry
end TangleStructTree
