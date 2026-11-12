-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_9
-- name    : RTStringIndex.Main.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:45.760564+00:00
-- url     : https://prove2.me/theorems/de385891-3b01-48fc-b137-cbe5f2801a5a
-- title:
--   Lemma 9 — w-links change only with a new lb-node or a new centroid path
-- statement:
--   Call a big node an **lb-node** if none of its children is big. The lemma says that a w-link needs to be added or changed only when a new lb-node is added to the big subtree or when a new centroid path is created.
--
--   Encode a centroid path by the interval from the parent of its head down to its tail. If big nodes are added without a new lb-node and without a new centroid path, this family of intervals is unchanged: such a node is created on an edge between big nodes and lies inside the interval of the path it joins.
--
--   The statement covers all such changes. Let the PST pass from the suffix tree of a text $Y$, in any admissible state with paths $D$, to the suffix tree of $B\,Y$ for any prepended letters $B$, keeping the same family $D$. Then for every path $g$ and every string $s$, neither $\mathrm{wlink}(g,s)$ nor whether it is $\mathrm{NULL}$ changes.
--
--   So the w-dictionaries need updates only when a new lb-node appears or a path is created, both of which happen during the gradual rebuilding of §11.
--
--   Differences from the source:
--   - reading: a w-link needs to be added or changed only when a new lb-node is added to the big subtree or when a new centroid path is created → if the family D of (parent(head), tail] intervals is unchanged while the text grows, no w-link changes; reason: a non-lb big node is added only as a node created on an edge between big nodes, which joins the path of its lower endpoint (p.11) and lies inside that path's interval; a new lb-node or a new path changes a tail or adds an interval
--   - generalization: one change of the big subtree → the suffix tree of Y replaced by that of B ++ Y for any letters B; the big set, levels and τ after the change are unconstrained and need not satisfy p.5; reason: the source's change is an instance; the w-links depend only on the tree and the path intervals
--   - generalization: w-links stored for the strings s_i, |s_i| ≤ d (p.24) → every string s; reason: covers the stored labels
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a centroid path with its nodes head(h), …, tail(h) and the edge into head(h) → the pair (parent(head(h)), tail(h)) (top none for the root path); its locations are those strictly below the top and at or above the tail; reason: Fig. 3 and p.8 assign the edge into head(h) to h; the pair determines the path's locations and nodes
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 9, p. 25, with the w-dictionaries, p. 24, and the insertion of u_b into the path of v, p. 11; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_PST

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 9.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.25. "We call a
big node an lb-node if none of its children is big. A w-link needs to be added or changed only when
a new lb-node is added to the big subtree or when a new centroid path is created."

**Formalization Note.** A path is the interval `(parent(head), tail]`. Adding big nodes without a
new lb-node and without a new centroid path leaves this family `D` unchanged: such a node is created
on an edge between big nodes and lies inside the interval of the path it joins (p.11). The
statement covers every such change: the PST passes from the suffix tree of `Y`, in any admissible
state, to the suffix tree of `B ++ Y` for any prepended letters `B`, with the same family `D`, and
then no w-link changes. The big set, the levels and `τ` after the change play no role, and the
state after the change need not be admissible. -/
theorem lemma_9 (Y B : List ℕ) (τ : ℝ) (Big : Set (List Chr)) (D : Finset CPath)
    (lev : CPath → ℕ) (hadm : Admissible (sufSet Y) τ Big D lev) :
    ∀ g ∈ D, ∀ s : List Chr,
      (∀ h', IsWLinkTarget (sufSet Y) D g s h' ↔ IsWLinkTarget (sufSet (B ++ Y)) D g s h') ∧
      (wlinkNull (sufSet Y) D g s ↔ wlinkNull (sufSet (B ++ Y)) D g s) := by sorry

end RTStringIndex.Main
