-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_G_1
-- name    : SunMinCut.Cactus.lemma_G_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:07.498254+00:00
-- url     : https://prove2.me/theorems/181710c8-757d-47aa-bcf7-de8f916d9e77
-- title:
--   Lemma G.1 — candidate completeness and noncrossing
-- statement:
--   Let an objective graph on the ordered vertices $0,1,\dots,k$ with $k\ge2$ have records $uv$, $u<v$, of nonnegative weight; $d_i=w(\delta\{i,\dots,k\})$, $h_{ij}=\sum_{u<i<j\le v}w_{uv}$, $F(i,j)=d_i+d_j-2h_{ij}$ for $1\le i<j\le k$. Give index $i\in\{1,\dots,k\}$ the key $(d_i,i)$ (lexicographic) and call $(a,b)$ a candidate pair if $a$ is the nearest smaller key to the left of $b$ or $b$ the nearest smaller key to the right of $a$. Then some candidate pair minimizes $F$ over every pair $1\le i<j\le k$, and the open arcs $(a,b)$ of all candidate pairs form a laminar family (any two are nested or disjoint).
--
--   Differences from the source:
--   - encoding: open arcs of candidate pairs → real open intervals (a, b); reason: the arcs of the ordered positions
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma G.1, p. 45

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Intervals

namespace SunMinCut.Cactus

/-- **Lemma G.1 (Candidate completeness and noncrossing)**, Sun 2026,
doi:10.5281/zenodo.23915020, p. 45: for a nonnegative objective graph on the ordered vertices
`0, …, k` with `k ≥ 2`, some candidate pair (an index with its nearest smaller key `(d_i, i)` on
either side) minimizes `F` over every pair `1 ≤ i < j ≤ k`, and the open arcs of all candidate
pairs form a laminar family. -/
theorem lemma_G_1 (k M : ℕ) (J : ObjGraph k M) (hJ : J.Valid) (hk : 2 ≤ k) :
    (∃ a b, J.IsCandidate a b ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ k → J.F a b ≤ J.F i j) ∧
    ∀ a c b d : ℕ, J.IsCandidate a c → J.IsCandidate b d →
      Set.Ioo (a : ℝ) c ⊆ Set.Ioo (b : ℝ) d ∨ Set.Ioo (b : ℝ) d ⊆ Set.Ioo (a : ℝ) c ∨
        Disjoint (Set.Ioo (a : ℝ) c) (Set.Ioo (b : ℝ) d) := by sorry

end SunMinCut.Cactus
