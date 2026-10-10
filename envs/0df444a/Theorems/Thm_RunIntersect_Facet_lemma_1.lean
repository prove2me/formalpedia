-- Prove2me | Theorems.Thm_RunIntersect_Facet_lemma_1
-- name    : RunIntersect.Facet.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:57.100989+00:00
-- url     : https://prove2.me/theorems/992d7081-3625-4913-86b9-d661a753415d
-- title:
--   Lemma 1, p. 1011 — leaves, first elements and deletion of contained sets for the running intersection property
-- statement:
--   Let $F$ be a multiset of subsets of a finite set with the running intersection property, and suppose $|F|\ge 2$. Then:
--
--   1. $F$ has at least two leaves, i.e. two elements of the multiset each of which is the last element of some running intersection ordering of $F$;
--   2. for every $f\in F$ there is a running intersection ordering of $F$ whose first element is $f$;
--   3. for every $f\in F$ such that $f\subseteq f'$ for some other element $f'$ of $F$, the multiset $F\setminus\{f\}$ has the running intersection property.
--
--   These are the basic manipulation rules for running intersection orderings, stated in various forms in the database literature (Beeri et al.); the paper uses them to reorder $\tilde E$ and to delete neighbors.
--
--   **Formalization Note** "Two leaves" is encoded as $F=f+g+R$ with $f$ and $g$ leaves, so the two leaves are two elements of the multiset (they may be equal sets occurring twice). In (iii), $f'$ ranges over $F$ with one copy of $f$ removed: with $f'=f$ itself the hypothesis would always hold and the statement would be false (for $F=\{ab,ac,bc,abc\}$ removing $abc$ leaves a triangle).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1011, Lemma 1

import Mathlib
import Definitions.Def_RunIntersect_Facet_Setting

namespace RunIntersect.Facet

/-- Lemma 1, p. 1011. Let `F` be a multiset with the running intersection property and
`|F| ≥ 2`. Then (i) `F` has at least two leaves (two elements of the multiset, possibly equal
sets); (ii) every `f ∈ F` is the first element of some running intersection ordering of `F`;
(iii) if `f ⊆ f'` for some other element `f'` of `F`, then `F ∖ {f}` has the running
intersection property. -/
theorem lemma_1 {α : Type*} [Fintype α] [DecidableEq α]
    (F : Multiset (Finset α)) (hF : HasRIP F) (h2 : 2 ≤ Multiset.card F) :
    (∃ f g : Finset α, ∃ R : Multiset (Finset α),
        F = f ::ₘ g ::ₘ R ∧ IsLeaf F f ∧ IsLeaf F g) ∧
    (∀ f ∈ F, ∃ l : List (Finset α),
        (l : Multiset (Finset α)) = F ∧ IsRIOrder l ∧ l.head? = some f) ∧
    (∀ f ∈ F, (∃ f' ∈ F.erase f, f ⊆ f') → HasRIP (F.erase f)) := by sorry

end RunIntersect.Facet
