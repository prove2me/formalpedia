-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_3
-- name    : RTStringIndex.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:26.194001+00:00
-- url     : https://prove2.me/theorems/8913009f-2156-4090-b49a-266b6df7f68a
-- title:
--   Lemma 3 — $|\mathrm{LCP}(S_i,\mathrm{label}(u'))|$ from one suffix link and one LCA
-- statement:
--   Let $A=a_1\cdots a_d$, $S_{\mathrm{init}}$, $1\le i\le d$ and $S_i=a_{d-i+1}\cdots a_dS_{\mathrm{init}}$ be as in §5. Let the PST be the suffix tree of $S_{i-1}$, and let $l_{i-1}$ be its leaf holding $S_{i-1}$. Let $u'$ be an internal node whose label starts with $a_{d-i+1}$, and let $l'_i$ be any leaf below $u'$. Then
--   $$|\mathrm{LCP}(S_i,\mathrm{label}(u'))|=\min\bigl(\mathrm{strdepth}(u'),\,t+1\bigr),\qquad t=\mathrm{strdepth}\bigl(\mathrm{lca}(l_{i-1},\mathrm{slink}(l'_i))\bigr).$$
--
--   The insertion procedure of §5 applies this lemma $O(1)$ times per new suffix to find where $S_i$ leaves a centroid path or enters a small subtree, at the cost of one suffix link and one lowest-common-ancestor query each time.
--
--   Differences from the source:
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a_{d−i+1} → A[d − i] (0-based), the first letter of S_i; reason: index convention; same instances
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 3, p. 10; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_SuffixTree

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 3.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.10. "Suppose
that label(u′) starts with a_{d−i+1} for some internal node u′ in the PST. Let l′_i denote an
arbitrary leaf descendant of u′. Then |LCP(S_i, label(u′))| = min(strdepth(u′), t + 1) for
t = strdepth(lca(l_{i−1}, slink(l′_i)))."

**Formalization Note.** `A = a_1 ⋯ a_d`, `X = S_init`, `1 ≤ i ≤ d`; the PST is the suffix tree of
`S_{i−1}`, whose leaf `l_{i−1}` is `S_{i−1}$`. Nodes are identified with their labels, `slink`
removes the first symbol, and the string depth of the `lca` of two leaves is the length of their
longest common prefix. `a_{d−i+1}` is `A[d − i]` (`0`-based). -/
theorem lemma_3 (A X : List ℕ) (i : ℕ) (hi1 : 1 ≤ i) (hid : i ≤ A.length)
    (u' : List Chr) (hu' : IsInternal (sufSet (Sk A X (i - 1))) u')
    (hstart : ∃ a, A[A.length - i]? = some a ∧ u'.head? = some (a : Chr))
    (l' : List Chr) (hl' : l' ∈ sufSet (Sk A X (i - 1))) (hdesc : u' <+: l') :
    lcpLen (term (Sk A X i)) u' =
      min u'.length (lcpLen (term (Sk A X (i - 1))) l'.tail + 1) := by sorry

end RTStringIndex.Main
