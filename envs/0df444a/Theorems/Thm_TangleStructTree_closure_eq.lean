-- Prove2me | Theorems.Thm_TangleStructTree_closure_eq
-- name    : TangleStructTree.closure_eq
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:39.179922+00:00
-- url     : https://prove2.me/theorems/2ee71a62-5cb8-47bb-ad81-badaa4b1205c
-- title:
--   §2 closure identity: $\lfloor\sigma\rfloor=\sigma\cup\{\vec s:\exists\,\vec r\in\sigma,\ r\ne s,\ \vec s>\vec r\}$
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system and let $\sigma\subseteq\vec S$ be consistent. Then, for every $\vec s\notin\sigma$, $\sigma$ requires $\vec s$ if and only if there exists $\vec r\in\sigma$ such that $r\ne s$ and $\vec s>\vec r$. Consequently
--   $$
--   \lfloor\sigma\rfloor=\sigma\cup\{\vec s\in\vec S:\exists\,\vec r\in\sigma\text{ such that } r\ne s\text{ and }\vec s>\vec r\}.
--   $$
--
--   This identity explains the name "(upward) closure" and is the form of $\lfloor\sigma\rfloor$ used in all later arguments about separation trees.
--
--   Differences from the source: none.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.4 (PDF 15), unnumbered identity after the definition of the closure

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

/-- **Closure identity** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4 (PDF 15)): for a
consistent `σ ⊆ S⃗`, `σ` requires `s⃗ ∉ σ` if and only if there exists an `r⃗ ∈ σ` such that `r ≠ s`
and `s⃗ > r⃗`; thus `⌊σ⌋ = σ ∪ {s⃗ ∈ S⃗ : ∃ r⃗ ∈ σ such that r ≠ s and s⃗ > r⃗}`.

**Formalization Note** `r ≠ s` (unoriented) is `r ≠ x ∧ r ≠ x∗`. The hypothesis that `σ` is
consistent is the paper's: "required" is defined for consistent `σ`. -/
theorem closure_eq (σ : Set E) (hσ : IsConsistent σ) :
    (∀ x : E, x ∉ σ → (Requires σ x ↔ ∃ r ∈ σ, (r ≠ x ∧ r ≠ rev x) ∧ r < x)) ∧
      sepClosure σ = σ ∪ {x | ∃ r ∈ σ, (r ≠ x ∧ r ≠ rev x) ∧ r < x} := by sorry
end TangleStructTree
