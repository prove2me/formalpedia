-- Prove2me | Theorems.Thm_RTStringIndex_Main_lemma_6
-- name    : RTStringIndex.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:51:04.047487+00:00
-- url     : https://prove2.me/theorems/8b043b2e-213e-476f-8dee-86749ae49b6f
-- title:
--   Lemma 6 — significant leaves of a block carry $O(\log^3 n)$ distinct marks
-- statement:
--   Fix a constant $K$. There is a constant $C$ with the following property. Let $n$ be the current length of the text and $T$ a main text with $|T|\le n$. Take any admissible PST state of $T$ with $\tau=\log_2^5n$, any leaf list $L_L$, and any block $B$ of $L_L$ with at most $K\log_2^5n$ leaves. With $\rho=\log_2^2n$, the significant leaves of $B$ are marked with at most
--   $$C\log_2^3 n$$
--   distinct symbols.
--
--   This is what keeps the fast predecessor structures small enough to be updated within the $O(\tau)$ budget when a block is split (§6, p.17).
--
--   **Formalization Note** For $n\le 1$, $\tau=0$ and no admissible state exists, so the bound is vacuous there.
--
--   Differences from the source:
--   - generalization: blocks of size Θ(log⁵ n) → for every constant K, every block with at most K log₂⁵ n leaves (C depends on K); reason: the algorithm's blocks have at most 7τ/4 leaves (p.17), so K = 7/4 is an instance; the lower size bound plays no role
--   - encoding: n, the current length of the text; log → n is any natural number with |T| ≤ n (the main text is part of the text); log is log₂; reason: §2 measures n as the whole text; p.23 writes log₂
--   - generalization: the PST state maintained by the algorithm → every big/small partition and centroid decomposition satisfying p.5 with τ = log₂⁵ n, and every leaf list; reason: the decomposition and the order inside groups are not unique
--   - encoding: suffix-tree nodes and locations (explicit or implicit), label, strdepth, slink, lca → a location is its label, a string over $\mathbb N\cup\{\$\}$ ($\$=\top$); the tree of a text $x$ is the compacted trie of the $|x|+1$ suffixes of $x\$$; strdepth is length, slink drops the first symbol, the lca of two nodes is their longest common prefix; reason: the source fixes no terminator; every suffix must be a leaf (§8 uses a terminal \$), and the label determines the location
--   - encoding: a centroid path with its nodes head(h), …, tail(h) and the edge into head(h) → the pair (parent(head(h)), tail(h)) (top none for the root path); its locations are those strictly below the top and at or above the tail; reason: Fig. 3 and p.8 assign the edge into head(h) to h; the pair determines the path's locations and nodes
-- source:
--   Gregory Kucherov, Yakov Nekrich, Real-Time String Indexing in Optimal Time, STOC 2027 submission #1543 (October 2026), Lemma 6, p. 15, with the block size Θ(log⁵ n), p. 14, and the parameters τ, ρ, p. 4; PDF SHA256 71c79bb80cc4d3fcb625decd72e0891e6b6178c09cb94001a67c6abfb63052f0

import Mathlib
import Definitions.Def_RTStringIndex_Main_Leaves

set_option autoImplicit false

namespace RTStringIndex.Main

/-- **Lemma 6.** Kucherov, Nekrich, STOC 2027 submission #1543 (October 2026), p.15. "In any block
B, significant leaves are marked with O(log³ n) distinct symbols." p.14: "The list L_L is divided
into blocks of size Θ(log⁵ n)"; p.4: τ = log⁵ n, ρ = log² n.

**Formalization Note.** For every block-size constant `K` there is a constant `C` such that, for
every `n`, every main text `T` with `|T| ≤ n` (`n` is the current length of the whole text), every
admissible PST state with `τ = log₂⁵ n`, every leaf list `L_L` and every block `B` of `L_L` with at
most `K log₂⁵ n` leaves, the significant leaves of `B` (with `ρ = log₂² n`) carry at most
`C log₂³ n` distinct marks. At `n ≤ 1`, `τ = 0` and no admissible state exists. -/
theorem lemma_6 (K : ℝ) :
    ∃ C : ℝ, ∀ (n : ℕ) (T : List ℕ), T.length ≤ n →
      ∀ (Big : Set (List Chr)) (D : Finset CPath) (lev : CPath → ℕ),
        Admissible (sufSet T) (tauPar n) Big D lev →
        ∀ pos : List Chr → ℕ, IsLeafList (sufSet T) Big D pos →
        ∀ lo hi : ℕ, ((block (sufSet T) pos lo hi).card : ℝ) ≤ K * tauPar n →
          ((sigSymbols T Big D (rhoPar n) (block (sufSet T) pos lo hi)).card : ℝ) ≤
            C * Real.logb 2 n ^ 3 := by sorry

end RTStringIndex.Main
