-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_8
-- name    : RTStringIndex.Main.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:36.549454+00:00
-- url     : https://prove2.me/theorems/94f1ce3c-4aa9-4c02-8588-433b4828b784
-- title:
--   Lemma 8 — shallow matches of $S_i$ propagate to $S_j$, $j\ge i$
-- statement:
--   Let $T$ be the main text, $L$ the set of labels of the nodes of its suffix tree of weight at least $2\tau$, and $S$ the set of its suffixes. Let $A=a_1\cdots a_d$ be the prepended block and $S_k=a_{d-k+1}\cdots a_dS_{\mathrm{init}}$. For $1\le i\le j\le d$:
--
--   1. if $|\mathrm{LCP}(S_i,L)|<i$, then $|\mathrm{LCP}(S_j,L)|<j$;
--   2. if $|\mathrm{LCP}(S_i,S)|<i$, then $|\mathrm{LCP}(S_j,S)|<j$.
--
--   In §7 this lets the algorithm, once one new suffix has only a shallow match, treat all later suffixes of the round in a single final phase of $O(d)$ time.
--
--   Differences from the source:
--   - generalization: T the main text at the time of §7, with S_init its content and τ = log⁵ n → arbitrary texts T and S_init and an arbitrary real τ; reason: the statement holds for every such choice, so it specializes to the source's
--   - encoding: L, the labels of nodes of weight at least 2τ → labels over ℕ ∪ {$}; S_i is compared letter by letter; reason: the suffix-tree strings carry the terminator; same instances
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 8, p. 18, with the definitions of L, S, A, p. 18; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_SuffixTree

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 8.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.18. "For
1 ≤ i ≤ j ≤ d: (a) if |LCP(S_i, L)| < i, then |LCP(S_j, L)| < j; (b) if |LCP(S_i, S)| < i, then
|LCP(S_j, S)| < j." p.18: "Let L denote the set of labels for all nodes with weight at least 2τ.
Let S denote the set of all suffixes in the main text T. Let A = a_1 a_2 ⋯ a_d denote the block of
prepended symbols; thus … S_i = A[d − i + 1..d] S_init."

**Formalization Note.** `L` is `heavyLabels` of the suffix tree of the main text `T` (strings over
`Chr`, so `S_i` is compared letter by letter), `S` is the set of nonempty suffixes of `T`. The main
text `T`, the text `S_init = X` and the threshold `τ` are arbitrary. -/
theorem lemma_8 (T X A : List ℕ) (τ : ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j)
    (hjd : j ≤ A.length) :
    (lcpSet ((Sk A X i).map (fun a => (a : Chr))) (heavyLabels (sufSet T) τ) < i →
      lcpSet ((Sk A X j).map (fun a => (a : Chr))) (heavyLabels (sufSet T) τ) < j) ∧
    (lcpSet (Sk A X i) (suffixes T) < i → lcpSet (Sk A X j) (suffixes T) < j) := by sorry

end RTStringIndex.Main
