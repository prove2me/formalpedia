-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_1
-- name    : RTStringIndex.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:31.114337+00:00
-- url     : https://prove2.me/theorems/ec735e43-1b59-4cac-982b-b51ada7e1667
-- title:
--   Lemma 1 — $O(1)$-time access to the $k$-th symbol of $\mathrm{label}(h)$
-- statement:
--   Let $h$ be a centroid path of an admissible PST of a text $T$, and let $\mathrm{leaf}(h)$ hold the suffix $T[i_h..]$, a leaf below $\mathrm{tail}(h)$. Store $T\$$ in an array, and store at the record of $h$ the numbers $i_h$ and $t=\mathrm{strdepth}(\mathrm{parent}(\mathrm{head}(h)))$. Then the $k$-th symbol of $\mathrm{label}(h)$, for $1\le k\le|\mathrm{label}(h)|$, can be retrieved in $O(1)$ time; it is the symbol $T[i_h+t+k-1]$ (1-based).
--
--   Precisely: there are one word-RAM program $Q$ and one constant $C$ with the following property. For every text, every admissible state, every path $h$, every such $k$ and every word size $W$ that fits the stored values, $Q$ is started on the input words (array base, record address, $k$), with the array and the record placed at or above $C$. On every random tape it then halts within $C$ steps, having written exactly the code of the $k$-th symbol of $\mathrm{label}(h)$.
--
--   The search for the locus of a pattern (§4) and the matching-statistics scans of §7 and §9 compare pattern symbols with symbols on centroid paths through this access.
--
--   Differences from the source:
--   - reading: we can retrieve the k-th symbol of label(h) in time O(1) → one fixed word-RAM program, run on the inputs (array base, record address, k) from a memory holding T$ as an array and the record (i_h, strdepth(parent(head(h)))), halts within C steps on every tape with exactly the symbol's code as output; reason: the source asserts O(1) time for its stored representation without fixing a memory layout; the proof uses exactly these two stored numbers and the text array
--   - encoding: the symbols of T, 1-based positions, and k-th symbol T[i_h + t + k − 1] → T$ stored from cell base with letter a as a + 1 and $ as 0; i_h is 0-based; the output is the code of label(h)[k−1] (0-based); reason: a word layout; same instances
--   - encoding: the word RAM of Theorem 1 → the machine of DynConnWC_Program; the layout lies at or above the program's work cells (address ≥ C) and every stored value is below 2^W; reason: the program needs scratch cells; same instances
--   - generalization: the PST state maintained by the algorithm, with τ = log⁵ n → every big/small partition and centroid decomposition satisfying the conditions of p.5, for every real threshold τ; reason: the algorithm's state satisfies these conditions; the decomposition is not unique and the statement covers all of them
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a centroid path with its nodes head(h), …, tail(h) and the edge into head(h) → the pair (parent(head(h)), tail(h)) (top none for the root path); its locations are those strictly below the top and at or above the tail; reason: Fig. 3 and p.8 assign the edge into head(h) to h; the pair determines the path's locations and nodes
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 1, p. 7, with the identity label(h) = T[i_h + f_1 .. i_h + f_2 − 1] stated before it, p. 7; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_PST
import Definitions.Def_RTStringIndex_Main_Machine

set_option autoImplicit false

open DynConnWC

namespace RTStringIndex.Main

/-- **Lemma 1.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.7. "For a
centroid path h and an integer k, we can retrieve the k-th symbol on the label of h in time O(1)."
p.7: "label(h) = T[i_h + f_1 .. i_h + f_2 − 1], where the suffix stored in leaf(h) is T[i_h..],
f_1 = strdepth(parent(head(h))), and f_2 = strdepth(tail(h))".

**Formalization Note.** Memory layout: the symbols of `T$` are stored in the array starting at
cell `base` (`symCode`: letter `a` as `a + 1`, `$` as `0`), and the record of `h` at cell `rec`
holds `i_h` (the `0`-based start of the suffix of `leaf(h)`, a leaf below `tail(h)`) and, at
`rec + 1`, `strdepth(parent(head(h)))`. One program `Q` and one constant `C` serve every text,
every admissible PST state, every path and every `k` with `1 ≤ k ≤ |label(h)|`: started on the
input words `base, rec, k`, it halts within `C` steps on every tape, having written exactly the
code of the `k`-th symbol of `label(h)`. The program's own work cells are below `C`, so the layout
starts at or above `C`; all stored values fit in a `W`-bit word. -/
theorem lemma_1 :
    ∃ (Q : Program) (C : ℕ),
      ∀ (T : List ℕ) (τ : ℝ) (Big : Set (List Chr)) (D : Finset CPath) (lev : CPath → ℕ),
        Admissible (sufSet T) τ Big D lev →
        ∀ h ∈ D, ∀ ih : ℕ, ih ≤ T.length → h.2 <+: term (T.drop ih) →
        ∀ k : ℕ, 1 ≤ k → k ≤ (pathLabel h).length →
        ∀ (W : ℕ) (mem : ℕ → BitVec W) (base rec : ℕ),
          C ≤ base → C ≤ rec → base + T.length + 1 < 2 ^ W → rec + 2 < 2 ^ W →
          (∀ a ∈ T, a + 1 < 2 ^ W) →
          (∀ (j : ℕ) (hj : j < (term T).length),
            mem (base + j) = BitVec.ofNat W (symCode ((term T)[j]'hj))) →
          mem rec = BitVec.ofNat W ih →
          mem (rec + 1) = BitVec.ofNat W (topDepth h) →
          ∀ ω : ℕ → Fin (2 ^ W), ∃ t ≤ C,
            Halted Q (confFrom W Q mem [base, rec, k] ω t) ∧
            ∃ hk : k - 1 < (pathLabel h).length,
              (confFrom W Q mem [base, rec, k] ω t).output =
                [symCode ((pathLabel h)[k - 1]'hk)] := by sorry

end RTStringIndex.Main
