-- Prove2me | Theorems.Thm_SingleOrSample_lemma_B_1
-- name    : SingleOrSample.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:47:29.300903+00:00
-- url     : https://prove2.me/theorems/0fab0575-36d9-46b3-8bed-12c345e34bbf
-- title:
--   Lemma B.1 — single-round SwR has upper-cylinder domination
-- statement:
--   Let $G$ be a nonempty finite set and $A\sim\mathrm{SwR}(G,p)$ with $p\in[0,1]$. For every fixed $T\subseteq G$,
--   $$\Pr[T\subseteq A]\le p^{|T|}.$$
--   The bound also holds when $p|G|$ is not an integer. It is the base case of the adaptive bound of Lemma B.2.
--
--   Differences from the source: none.
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.1, p.30

import Mathlib
import Definitions.Def_SingleOrSample_swr

namespace SingleOrSample

/-- **Lemma B.1** (Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Lemma B.1, p.30). For nonempty `G`, `A ∼ SwR(G, p)` and fixed `T ⊆ G`,
`Pr[T ⊆ A] ≤ p^|T|`, also when `p|G|` is not an integer. -/
theorem lemma_B_1 {α : Type*} (G : Finset α) (hG : G.Nonempty) (p : unitInterval) (T : Finset α)
    (hT : T ⊆ G) :
    (swr G p).toOuterMeasure {A | T ⊆ A} ≤ ENNReal.ofReal ((p : ℝ) ^ T.card) := by sorry

end SingleOrSample
