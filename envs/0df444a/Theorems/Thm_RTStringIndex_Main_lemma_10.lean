-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_10
-- name    : RTStringIndex.Main.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:56.352144+00:00
-- url     : https://prove2.me/theorems/6d01cf45-32c3-4db2-ab23-666507b689f2
-- title:
--   Lemma 10 — inserting $S_i$ changes no w-link
-- statement:
--   Let $A=a_1\cdots a_d$, $S_{\mathrm{init}}$ and $1\le i\le d$ be as in §5, and consider any admissible state of the PST of $S_{i-1}$ with centroid paths $D$. The insertion of $S_i$ described in §5 creates the leaf of $S_i$ and possibly a node $u_b$ on an edge $(u,v)$. If $v$ is big, $u_b$ joins the path of $v$; otherwise it joins no path. No rebuilding is performed.
--
--   The lemma states that for every centroid path $g$ and every string $s$, the insertion changes neither $\mathrm{wlink}(g,s)$ nor whether it is $\mathrm{NULL}$.
--
--   The insertion procedure of §5 therefore needs no w-link update for the suffixes it inserts; w-links change only when the big subtree itself is rebuilt (Lemma 9).
--
--   **Formalization Note** In the encoding of a path by (parent of head, tail), the state after the insertion is the suffix tree of $S_i$ with the same family $D$.
--
--   Differences from the source:
--   - generalization: the insertion of S_i performed by §5 after the w-link search of Fig. 5 found h_i → the passage from the suffix tree of S_{i−1} to that of S_i, from any admissible state, with no precondition on the search; reason: the resulting tree and paths are the same whichever way the insertion position was found; the §5 case is an instance
--   - generalization: wlink(g, s) for a nonempty string s (definition, p.8) → every string s, including the empty one; reason: covers the source's strings; the empty string adds a case
--   - encoding: u_b is added to the centroid path of v when v is big (p.11) → the same family D of (parent(head), tail) intervals: u_b lies in the interval of v's path exactly when v is big; reason: the interval encoding performs this assignment; same instances
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 10, p. 25 (cited on p. 11), with the insertion procedure of §5, p. 11; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_PST

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 10.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.25 (cited on
p.11). "The insertion of a suffix S_i described in Section 5, before any rebuilding work is
performed, does not change wlink(g, s) for any centroid path g and any string s."

**Formalization Note.** `A = a_1 ⋯ a_d`, `X = S_init`, `1 ≤ i ≤ d`. Before the insertion the PST
is the suffix tree of `S_{i−1}`, in any admissible state with paths `D`; the insertion of §5
(p.11) creates the leaf of `S_i` and possibly a node `u_b` on an edge `(u, v)`, which joins the
path of `v` when `v` is big. In the `(top, tail)` encoding of paths this is the suffix tree of
`S_i` with the same family `D`: `u_b` lies in the interval of `v`'s path exactly when `v` is big,
and the new leaf lies on no path. No rebuilding is performed. For every path `g` and every string
`s`, the w-link target and its being `NULL` are the same before and after. -/
theorem lemma_10 (A X : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hid : i ≤ A.length) (τ : ℝ)
    (Big : Set (List Chr)) (D : Finset CPath) (lev : CPath → ℕ)
    (hadm : Admissible (sufSet (Sk A X (i - 1))) τ Big D lev) :
    ∀ g ∈ D, ∀ s : List Chr,
      (∀ h', IsWLinkTarget (sufSet (Sk A X (i - 1))) D g s h' ↔
        IsWLinkTarget (sufSet (Sk A X i)) D g s h') ∧
      (wlinkNull (sufSet (Sk A X (i - 1))) D g s ↔ wlinkNull (sufSet (Sk A X i)) D g s) := by sorry

end RTStringIndex.Main
