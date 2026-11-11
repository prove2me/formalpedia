-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_6
-- name    : RandDelMatroid.Indep.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:30:16.478073+00:00
-- url     : https://prove2.me/theorems/3b9b4490-6882-4f4d-890f-4bc680967bbc
-- title:
--   Lemma 6 — linear size of an unordered decomposition tree
-- statement:
--   Let $M=(E,\mathcal I)$ be a regular matroid with $m=|E|$, let $T$ be an unordered decomposition tree of $M$, and let $E_u$ be the ground set of the matroid at node $u$. Then
--
--   $$|V(T)|\le 2m\qquad\text{and}\qquad \sum_{u\in V(T)}|E_u|\ \le\ m+6\,(|V(T)|-1).$$
--
--   The paper states the second bound as $\sum_u|E_u|=O(m)$; its proof establishes $\sum_u|E_u|=m+2\sum_{e\in E(T)}|S_e|\le m+6(|V(T)|-1)$, which with the first bound gives at most $13m$. The lemma bounds the number of nodes in the final union bound of Theorem 1.
--
--   Differences from the source:
--   - reading: ∑_u |E_u| = O(m) → ∑_u |E_u| ≤ m + 6 (|V(T)| − 1); reason: the explicit bound the paper's proof establishes (p. 14); it implies O(m) since |V(T)| ≤ 2m
--   - encoding: regular = representable over every field → representable over every field F : Type; reason: Lean quantifies over fields in the base universe; this is a weaker hypothesis on M, so the statement covers every regular matroid
--   - encoding: M_T is isomorphic to M (Definition 11.4), elements identified → M is a matroid on the tree's element type with M = M_T; reason: the paper identifies M_T with M ('After identifying M_T with M', p. 12); every tree of an abstract M is one of an isomorphic copy on the tree's type
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 14, Lemma 6 (bound from its proof, p. 14)

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_DecompTree

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 6 (p. 14), with the explicit bound of its proof. For an unordered decomposition tree `T`
of a regular matroid `M` with `m = |E|` elements, `|V(T)| ≤ 2m` and
`∑_{u ∈ V(T)} |E_u| ≤ m + 6 (|V(T)| - 1)` (the paper writes `O(m)`). -/
theorem lemma_6 {β ι : Type} [Fintype ι] (M : Matroid β) (T : SimpleGraph ι)
    (Mn : ι → Matroid β) (hT : IsUnorderedDecompTree M T Mn) :
    Fintype.card ι ≤ 2 * M.E.ncard ∧
      ∑ u, (Mn u).E.ncard ≤ M.E.ncard + 6 * (Fintype.card ι - 1) := by sorry

end RandDelMatroid.Indep
