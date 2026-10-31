-- Prove2me | Theorems.Thm_SteinerCutDominants_lemma_3
-- name    : SteinerCutDominants.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:28.052324+00:00
-- url     : https://prove2.me/theorems/1d81a1c7-8efe-45a1-a1ce-5610b4779b2f
-- title:
--   Lemma 3: uncrossing strictly shrinks $I(S,\mathcal L)$
-- statement:
--   Let $\mathcal L$ be a laminar family of subsets of $V$, and let $L\in\mathcal L$ and $S\subseteq V$ intersect. Then
--   $$
--   I(S\cap L,\mathcal L),\quad I(S\cup L,\mathcal L),\quad I(S\setminus L,\mathcal L),\quad I(L\setminus S,\mathcal L)\ \subsetneq\ I(S,\mathcal L).
--   $$
--   This is the measure of progress in the uncrossing argument of Theorem 1.
--
--   Differences from the source: none.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, Lemma 3, p.7

import Mathlib
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_SteinerCutDominants_intersecting

namespace SteinerCutDominants

/-- **Lemma 3** (Conforti, Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, p.7). If `𝓛` is a
laminar family of subsets of `V`, and `L ∈ 𝓛` and `S ⊆ V` intersect, then each of `I(S ∩ L, 𝓛)`,
`I(S ∪ L, 𝓛)`, `I(S \ L, 𝓛)`, `I(L \ S, 𝓛)` is a proper subset of `I(S, 𝓛)`. -/
theorem lemma_3 {V : Type} [DecidableEq V] (𝓛 : Finset (Finset V)) (h𝓛 : IsLaminar 𝓛)
    (L S : Finset V) (hL : L ∈ 𝓛) (hLS : Intersect S L) :
    intersecting (S ∩ L) 𝓛 ⊂ intersecting S 𝓛 ∧ intersecting (S ∪ L) 𝓛 ⊂ intersecting S 𝓛 ∧
      intersecting (S \ L) 𝓛 ⊂ intersecting S 𝓛 ∧ intersecting (L \ S) 𝓛 ⊂ intersecting S 𝓛 := by sorry

end SteinerCutDominants
