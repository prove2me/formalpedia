-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_2
-- name    : RTStringIndex.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:45.898535+00:00
-- url     : https://prove2.me/theorems/f7f8fd03-d364-4601-9cdd-e7344375f75a
-- title:
--   Lemma 2 — the insertion location of $S_i$ is on $\mathrm{wlink}(h_i,s_i)$ or on a leaf path below it
-- statement:
--   Let $A=a_1\cdots a_d$ be the prepended block, $S_{\mathrm{init}}$ the main text, and $1\le i\le d$. Write $s_i=a_{d-i+1}\cdots a_d$ and $S_i=s_iS_{\mathrm{init}}$. Consider any admissible state of the PST of $S_{i-1}$ (the tree before $S_i$ is inserted). Let $h_0$ be the path of the lowest big ancestor of the leaf $l_0$ of $S_{\mathrm{init}}$, and let $h_i$ be the lowest ancestor-or-self of $h_0$ in the centroid-path tree with $\mathrm{wlink}(h_i,s_i)\ne\mathrm{NULL}$. Let $h'_i=\mathrm{wlink}(h_i,s_i)$.
--
--   Let $\nu_a$ be the lowest ancestor location of $\mathrm{tail}(h'_i)$ whose label is a prefix of $S_i$, and let $\nu_l$ be the lowest location of the big subtree whose label is a prefix of $S_i$. Then one of the following holds:
--
--   1. $\nu_l$ is an ancestor of $\mathrm{tail}(h'_i)$ and $\nu_l=\nu_a$;
--   2. $\nu_a$ is an explicit node, and $\nu_l$ lies on a centroid path $h'_p$ with $\mathrm{parent}(\mathrm{head}(h'_p))=\nu_a$ that is a leaf of the centroid-path tree.
--
--   Hence $O(1)$ centroid paths have to be examined to find the location where $S_i$ leaves the big subtree. This bounds the per-suffix work of the insertion procedure of §5.
--
--   Differences from the source:
--   - reading: h_i: Fig. 5's lowest ancestor of h_{i−1} with wlink(h_i, s_i) ≠ NULL → the lowest ancestor-or-self of h_0 with wlink(h_i, s_i) ≠ NULL; reason: this is the form the proof uses (p.10); the two agree because a w-link labelled s_i yields one labelled s_{i−1}
--   - reading: h_0 computed at the start of the round → h_0 is the path of the lowest big ancestor of the leaf of S_init in the current state; reason: an insertion never changes the lowest big ancestor of l_0, so the source's h_0 is this one
--   - encoding: ν_a, the lowest ancestor location of tail(h′_i) matching a prefix of S_i → the longest common prefix of tail(h′_i) and S_i$; reason: a label containing $ cannot be a prefix of the new suffix; same location
--   - generalization: the PST state maintained by the algorithm, with τ = log⁵ n → every big/small partition and centroid decomposition satisfying the conditions of p.5, for every real threshold τ; reason: the algorithm's state satisfies these conditions; the decomposition is not unique and the statement covers all of them
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a centroid path with its nodes head(h), …, tail(h) and the edge into head(h) → the pair (parent(head(h)), tail(h)) (top none for the root path); its locations are those strictly below the top and at or above the tail; reason: Fig. 3 and p.8 assign the edge into head(h) to h; the pair determines the path's locations and nodes
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 2, p. 9, with Fig. 5, p. 9 and the proof, p. 10; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_PST

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 2.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.9. "Let
s_i = a_{d−i+1} ⋯ a_d, S_i = s_i S_init, and h′_i = wlink(h_i, s_i). Let ν_a be the lowest ancestor
location of tail(h′_i) that matches a prefix of S_i, and let ν_l be the lowest location in the big
subtree that matches a prefix of S_i. Either (i) ν_l is an ancestor of tail(h′_i) and ν_l = ν_a or
(ii) ν_a is a node and ν_l is a location on a centroid path h′_p such that parent(head(h′_p)) = ν_a,
and h′_p is a leaf of the centroid-path tree."

**Formalization Note.** The block is `A = a_1 ⋯ a_d`, the main text `X = S_init`, and
`1 ≤ i ≤ d`. The PST is the suffix tree of `S_{i−1}` (before `S_i` is inserted), in any
admissible state. `h_0` is the path of the lowest big ancestor of the leaf `l_0` of `S_init`, and
`h_i` is the lowest ancestor-or-self of `h_0` with `wlink(h_i, s_i) ≠ NULL` (the form used in the
proof, p.10). `ν_a` is the longest common prefix of `tail(h′_i)` and `S_i$`. -/
theorem lemma_2 (A X : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hid : i ≤ A.length) (τ : ℝ)
    (Big : Set (List Chr)) (D : Finset CPath) (lev : CPath → ℕ)
    (hadm : Admissible (sufSet (Sk A X (i - 1))) τ Big D lev)
    (h₀ : CPath) (hh₀ : IsPathOf Big D (term X) h₀)
    (hi : CPath) (hhi : PathAnc D hi h₀)
    (hlow : ∀ g, PathAnc D g h₀ → PathAnc D hi g → g ≠ hi →
      wlinkNull (sufSet (Sk A X (i - 1))) D g (sk A i))
    (hi' : CPath) (hlink : IsWLinkTarget (sufSet (Sk A X (i - 1))) D hi (sk A i) hi')
    (νa νl : List Chr) (hνa : νa = lcpStr hi'.2 (term (Sk A X i)))
    (hνl : IsLowestBigMatch D (term (Sk A X i)) νl) :
    (νl <+: hi'.2 ∧ νl = νa) ∨
      (IsNode (sufSet (Sk A X (i - 1))) νa ∧
        ∃ hp ∈ D, InPath hp νl ∧ hp.1 = some νa ∧ IsLeafPath D hp) := by sorry

end RTStringIndex.Main
