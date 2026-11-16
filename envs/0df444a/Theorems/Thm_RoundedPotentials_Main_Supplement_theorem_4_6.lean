-- Prove2me | Theorems.Thm_RoundedPotentials_Main_Supplement_theorem_4_6
-- name    : RoundedPotentials.Main.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:06:18.048759+00:00
-- url     : https://prove2.me/theorems/6bcfb90b-6127-4c2f-8cdb-17f314997af3
-- title:
--   Theorem 4.6 — Amortized Merlin–Arthur verification (Theorem 1.2)
-- statement:
--   Fix $c>0$ and an exponent $D$, so that capacities are polynomially bounded, $W\le n^D$. Let $G$ be a directed graph on $[n]$, $n\ge2$, with integer capacities in $[1,W]$ on its $m$ listed edges. Let $(s_a,t_a,p_a)_{a\le q}$ be a public list of $1\le q\le n(n-1)$ ordered pairs with $s_a\ne t_a$ and claimed integer values $p_a$.
--
--   There is a one-message Merlin–Arthur protocol, the same program for every instance, with constants $C,K$ depending only on $c$ and $D$. Let $L=\lfloor\log_2 n\rfloor+1$ and $T=C(m+qn)L^K$. The protocol satisfies:
--
--   1. **Time and space.** For every message, Arthur halts within $T$ steps and touches at most $CnL^K$ memory cells (words). When every claim lies in $[0,(n-1)W]$, his working space, the touched cells times the word size, is at most $CnL^K$ bits.
--   2. **Perfect completeness.** If every claim is true, some message of at most $Cqn(\lfloor\log_2(nW)\rfloor+1)$ bits is accepted for every coin outcome.
--   3. **Soundness.** If some claim is false, every message, fixed before the coins, is accepted with probability at most $n^{-c}$.
--
--   For a capacity-matrix input, a second program has the same properties with $T=C(n^2+qn)L^K$.
--
--   In particular, for $q=n(n-1)$, directed All-Pairs Max-Flow has $\widetilde O(n^3)$ verification time and $O_c(n^3\log n)$ proof bits, without fast matrix multiplication.
--
--   **Formalization Note** Time and space are measured on the published word RAM `DynConnWC.Program`, with the run notions of `MinKCutII_Main_Runs`. The word size is $K\lceil\log_2(\cdot)\rceil$ of the public instance and the time bound. Arthur's coins are the uniformly random tape words. Merlin's message consists of a header of a constant number $hl$ of words and one block of $bl(n,W)$ words per query. Arthur reads the header, the graph, and each query followed by its block.
--
--   Differences from the source:
--   - encoding: verification time and working space → steps, and touched cells × word size, on the published word RAM DynConnWC.Program with word size K⌈log₂(·)⌉ of the public instance and time bound; Õ(·) as C·(·)·(⌊log₂ n⌋+1)^K; reason: the machine model of the platform's operational ω; the instance fixes the words, so Merlin cannot enlarge them
--   - reading: Õ(n) bits of working space → at most C·n·L^K touched cells (words) for every input; at most C·n·L^K bits (cells × word size) when every claim lies in [0, (n−1)W]; reason: on the word RAM every input number occupies a word, so a superpolynomial false claim enlarges the word size Wd; claims in [0, (n−1)W], which include all true claims, keep Wd = O(log n), and Arthur rejects any other claim after one comparison
--   - encoding: one message read by Arthur → a header of hl words (a constant of the protocol) and one block of bl(n,W) words per query, read in the order header, graph, then each query's public words followed by its block; reason: this machine reads its input once in order; fixed part lengths keep the public words aligned for every message, and a malformed-length message is one the source rejects
--   - reading: polynomially bounded capacities (§1.1, "unless stated otherwise") → ∀ D, W ≤ n^D, with program and constants depending on c and D; reason: the standing assumption of §1.1 and Table 1
--   - encoding: G with m nonzero-capacity edges; claimed integer values → an edge list (base Instance) whose listed capacities are positive, m its length; claims in ℤ given as sign and absolute value words; reason: same instances
--   - reading: "In particular, directed All-Pairs Max-Flow has Õ(n³) verification time and O_c(n³ log n) proof bits" → not a separate conjunct: the capacity-matrix clause with q = n(n−1); reason: with q = n(n−1), n² + qn ≤ 2n³ and log₂(nW) ≤ (D+1)log₂ n + 1, so the bounds follow arithmetically for the same protocol
-- source:
--   Ohad Trabelsi, STOC 2027 submission #1650 (October 2026), p. 22, Theorem 4.6

import Mathlib
import Definitions.Def_RoundedPotentials_Main_Supplement_Verification

namespace RoundedPotentials.Main.Supplement

open RoundedPotentials.Main DynConnWC MinKCutII.Main MultStretchAPASP.Weighted

theorem theorem_4_6 (c : ℝ) (hc : 0 < c) (D : ℕ) :
    ∃ (P₁ P₂ : Program) (C K hl : ℕ) (bl : ℕ → ℕ → ℕ),
      -- edge-list input: time `Õ(m + qn)`
      (∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
        ∀ (I : Instance n W), (∀ e ∈ I.edges, 0 < e.2.2) →
        ∀ (Qs : List (Query n)), ValidQueries n Qs →
          let g := edgeListWords I
          let q := Qs.length
          let L : ℝ := Nat.log 2 n + 1
          let T : ℝ := C * (I.edges.length + q * n) * L ^ K
          let Wd := wordSize K (g ++ queryWords Qs) T
          (∀ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks →
            ∀ ω : ℕ → Fin (2 ^ Wd),
              HaltsWithin Wd P₁ (maInput g Qs header blocks) ω T ∧
              ∀ τ : ℕ, ((touchedBetween Wd P₁ (maInput g Qs header blocks) ω 0 τ).ncard : ℝ) ≤
                C * n * L ^ K ∧
                ((∀ a ∈ Qs, 0 ≤ a.2.2 ∧ a.2.2 ≤ ((n - 1) * W : ℕ)) →
                  ((touchedBetween Wd P₁ (maInput g Qs header blocks) ω 0 τ).ncard : ℝ) * Wd ≤
                    C * n * L ^ K)) ∧
          ((∀ a ∈ Qs, MaxValue I a.1 a.2.1 (a.2.2 : ℝ)) →
            ∃ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks ∧
              messageBits q header blocks ≤ C * q * n * (Nat.log 2 (n * W) + 1) ∧
              ∀ ω : ℕ → Fin (2 ^ Wd), Accepts Wd P₁ (maInput g Qs header blocks) ω) ∧
          ((∃ a ∈ Qs, ¬ MaxValue I a.1 a.2.1 (a.2.2 : ℝ)) →
            ∀ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks →
              tapeLaw Wd {ω | Accepts Wd P₁ (maInput g Qs header blocks) ω} ≤
                ENNReal.ofReal ((n : ℝ) ^ (-c)))) ∧
      -- capacity-matrix input: time `Õ(n² + qn)`
      (∀ (n W : ℕ), 2 ≤ n → 1 ≤ W → W ≤ n ^ D →
        ∀ (cap : Fin n → Fin n → ℕ), (∀ u v, cap u v ≤ W) →
        ∀ (Qs : List (Query n)), ValidQueries n Qs →
          let g := matrixWords n W cap
          let q := Qs.length
          let L : ℝ := Nat.log 2 n + 1
          let T : ℝ := C * (n ^ 2 + q * n) * L ^ K
          let Wd := wordSize K (g ++ queryWords Qs) T
          (∀ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks →
            ∀ ω : ℕ → Fin (2 ^ Wd),
              HaltsWithin Wd P₂ (maInput g Qs header blocks) ω T ∧
              ∀ τ : ℕ, ((touchedBetween Wd P₂ (maInput g Qs header blocks) ω 0 τ).ncard : ℝ) ≤
                C * n * L ^ K ∧
                ((∀ a ∈ Qs, 0 ≤ a.2.2 ∧ a.2.2 ≤ ((n - 1) * W : ℕ)) →
                  ((touchedBetween Wd P₂ (maInput g Qs header blocks) ω 0 τ).ncard : ℝ) * Wd ≤
                    C * n * L ^ K)) ∧
          ((∀ a ∈ Qs, MatrixMaxValue n W cap a.1 a.2.1 a.2.2) →
            ∃ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks ∧
              messageBits q header blocks ≤ C * q * n * (Nat.log 2 (n * W) + 1) ∧
              ∀ ω : ℕ → Fin (2 ^ Wd), Accepts Wd P₂ (maInput g Qs header blocks) ω) ∧
          ((∃ a ∈ Qs, ¬ MatrixMaxValue n W cap a.1 a.2.1 a.2.2) →
            ∀ (header : List ℕ) (blocks : ℕ → List ℕ), MAMessage hl (bl n W) q header blocks →
              tapeLaw Wd {ω | Accepts Wd P₂ (maInput g Qs header blocks) ω} ≤
                ENNReal.ofReal ((n : ℝ) ^ (-c)))) := by sorry

end RoundedPotentials.Main.Supplement
