-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_4
-- name    : RTStringIndex.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:50:42.450323+00:00
-- url     : https://prove2.me/theorems/75732e04-5a41-43af-b838-830661c4461c
-- title:
--   Lemma 4 — an optimal leaf $l_{\max}$ lies on one of six candidate paths
-- statement:
--   Consider any admissible PST state of a text, any leaf list $L_L$, a small subtree rooted at $a\cdot v$ with $\mathrm{slink}(a\cdot v)=v$, the set $R(v)$ of leaves below $v$ marked $a$, and any representative list $L_H$ of $R(v)$. Let $g_R(v)$ be the path of $v$, and let $l$ be a leaf below $v$ with $\mathrm{path}(l)=h$.
--
--   Let $h_1$ be a child of $h$ in the centroid-path tree maximizing $\mathrm{strdepth}(\mathrm{parent}(\mathrm{head}(h_1)))$, and let $l_1$ be any leaf below $\mathrm{head}(h_1)$. If $h$ is a leaf path, set $h_1=h$ and $l_1=l$. Let $l_p$ and $l_s$ be the predecessor and successor of $l_1$ in $L_H$, and put $h_p=\mathrm{path}(l_p)$, $h_s=\mathrm{path}(l_s)$.
--
--   Then some leaf $l_{\max}\in R(v)$ maximizing $\mathrm{strdepth}(\mathrm{lca}(x,l))$ over $x\in R(v)$ satisfies
--   $$\mathrm{path}(l_{\max})\in\{h,\;h_p,\;h_s,\;\mathrm{LCA}(h,h_p),\;\mathrm{LCA}(h,h_s),\;g_R(v)\},$$
--   where the LCAs are taken in the centroid-path tree and terms involving a nonexistent neighbour are omitted.
--
--   After two neighbour queries in $L_H$, this leaves a constant number of candidate paths, so inserting a suffix into a small subtree (§6) costs $O(1)$ beyond those queries.
--
--   Differences from the source:
--   - generalization: l = l_{i−1}, the leaf of the previously inserted suffix (p.14) → any leaf l below v; reason: the proof uses only that l lies below v (p.14), which l_{i−1} does
--   - reading: the child h_1 maximizing strdepth(parent(head(h_1))) → any child maximizing it; reason: the source does not say how ties are broken
--   - reading: g_R(v), the centroid path of v → the path of v's lowest big ancestor-or-self; reason: v may be small; this is the convention of §10 (p.24) and the use on p.15
--   - generalization: the leaf list L_L and the representatives maintained by the algorithm → every leaf list respecting the grouping in L_C order and every representative list; reason: the source allows an arbitrary order inside each group and an arbitrary representative
--   - encoding: children in L_C ordered by the lexicographic order of leaf(h_i) → siblings compared by the lexicographic order of their tails, with $ the largest symbol; reason: the subtrees of siblings are disjoint, so any leaves below them compare as their tails; the source does not place $ in the order of the main text
--   - generalization: the PST state maintained by the algorithm, with τ = log⁵ n → every big/small partition and centroid decomposition satisfying the conditions of p.5, for every real threshold τ; reason: the algorithm's state satisfies these conditions; the decomposition is not unique and the statement covers all of them
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a centroid path with its nodes head(h), …, tail(h) and the edge into head(h) → the pair (parent(head(h)), tail(h)) (top none for the root path); its locations are those strictly below the top and at or above the tail; reason: Fig. 3 and p.8 assign the edge into head(h) to h; the pair determines the path's locations and nodes
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 4, p. 13, with the definitions of L_C, L_L, H(v), L_H, p. 13; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_Leaves

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 4.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.13. "Let
path(l) = h and let h_1 denote the child of h in the centroid-path tree, such that the string depth
of parent(head(h_1)) is maximized. Let l_1 denote an arbitrary leaf descendant of head(h_1). If h is
a leaf path, we set h_1 = h and l_1 = l. Let l_p and l_s be the predecessor and successor of l_1 in
L_H, and write h_p = path(l_p) and h_s = path(l_s). Then an optimal leaf l_max, i.e., a leaf
x ∈ R(v) maximizing strdepth(lca(x, l)), can be chosen such that
path(l_max) ∈ {h, h_p, h_s, LCA(h, h_p), LCA(h, h_s), g_R(v)}. Here, LCAs of paths are taken in the
centroid-path tree, and terms involving nonexistent neighbors are omitted."

**Formalization Note.** The PST is the suffix tree of any text `Y`, in any admissible state, with
any leaf list `L_L` (`pos`) and any representative list `L_H` of `R(v)`. `a·v` is the root of a
small subtree and `v = slink(a·v)`, so `R(v)` is the set of leaves below `v` marked `a`; `l` is a
leaf below `v` (as the query leaf of p.14); `g_R(v)` is the path of `v` (of its lowest big
ancestor-or-self). `h_1` is any child of `h` maximizing `strdepth(parent(head(h_1)))`. The string
depth of `lca(x, l)` for leaves is the length of their longest common prefix. -/
theorem lemma_4 (Y : List ℕ) (τ : ℝ) (Big : Set (List Chr)) (D : Finset CPath)
    (lev : CPath → ℕ) (hadm : Admissible (sufSet Y) τ Big D lev)
    (pos : List Chr → ℕ) (hpos : IsLeafList (sufSet Y) Big D pos)
    (a : ℕ) (v : List Chr) (hroot : IsSmallRoot (sufSet Y) Big ((a : Chr) :: v))
    (l : List Chr) (hl : l ∈ sufSet Y) (hlv : v <+: l)
    (gR : CPath) (hgR : IsPathOf Big D v gR)
    (LH : Finset (List Chr)) (hLH : IsRepList Big D (Rset (sufSet Y) a v) gR LH)
    (h : CPath) (hh : IsPathOf Big D l h)
    (h₁ : CPath) (l₁ : List Chr)
    (hchoice : (IsLeafPath D h ∧ h₁ = h ∧ l₁ = l) ∨
      (¬ IsLeafPath D h ∧ IsPathParent D h h₁ ∧
        (∀ c, IsPathParent D h c → topDepth c ≤ topDepth h₁) ∧
        l₁ ∈ sufSet Y ∧ ∀ hd, IsHead (sufSet Y) h₁ hd → hd <+: l₁)) :
    ∃ x ∈ Rset (sufSet Y) a v,
      (∀ y ∈ Rset (sufSet Y) a v, lcpLen y l ≤ lcpLen x l) ∧
      ∃ g, IsPathOf Big D x g ∧
        (g = h ∨ g = gR ∨
          (∃ lp hp, IsPredIn pos LH l₁ lp ∧ IsPathOf Big D lp hp ∧ (g = hp ∨ IsPathLCA D h hp g)) ∨
          (∃ ls hs, IsSuccIn pos LH l₁ ls ∧ IsPathOf Big D ls hs ∧ (g = hs ∨ IsPathLCA D h hs g))) := by sorry

end RTStringIndex.Main
