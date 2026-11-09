-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_4
-- name    : ThreshRankBIS.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:02:31.07419+00:00
-- url     : https://prove2.me/theorems/9588304f-9185-4347-8a05-79f586edf5b6
-- title:
--   Lemma 4 — counting by the left part, $Z_G(\lambda)=\sum_{A\subseteq X}\lambda^{|A|}q^{n-|N(A)|}$
-- statement:
--   Let $G=(X\cup Y,E)$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$ and $d\ge1$, let $\lambda>0$ and $q=1+\lambda$. Then
--
--   $$
--   Z_G(\lambda)=\sum_{A\subseteq X}\lambda^{|A|}\,q^{\,n-|N(A)|}. \tag{4}
--   $$
--
--   The identity groups independent sets by their left part $A$: the right part is any subset of $Y\setminus N(A)$. It reduces every weight estimate of the paper to a sum over left sets, and the normalized form $Z_G(\lambda)/q^n=\sum_A\lambda^{|A|}q^{-|N(A)|}$ is the starting point of the container bound.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - generalization: the fugacity λ, rational where it is an algorithm input (p.3) → λ a real number with the same lower bound; reason: the statement is about the combinatorial weights only and holds for every real λ in the range; it specializes to rational λ
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 4, p.8, display (4)

import Mathlib
import Definitions.Def_ThreshRankBIS_closure
import Definitions.Def_ThreshRankBIS_hardcoreZ
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Lemma 4 (Counting by the left part)**, p.8. For every `λ > 0`,
`Z_G(λ) = ∑_{A ⊆ X} λ^{|A|} q^{n − |N(A)|}`, `q = 1 + λ` (display (4)).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 4, p.8.

**Formalization Note.** `G` is `HiddenPartition.bip E`, `d`-regular with `d ≥ 1` (the standing assumptions
of §2.1, p.7). `λ` is real (the paper's `λ` is rational only as an algorithm input).
`n − |N(A)|` is a natural-number difference, which is exact since `N(A) ⊆ Y` has at most `n`
elements. -/
theorem lemma_4 {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (lam : ℝ) (hlam : 0 < lam) :
    hardcoreZ E lam = ∑ A : Finset (Fin n), lam ^ #A * (1 + lam) ^ (n - #(nbhd E A)) := by sorry

end ThreshRankBIS
