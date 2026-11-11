-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_3_11
-- name    : SingleExpBisect.Main.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:41:55.893989+00:00
-- url     : https://prove2.me/theorems/a1f4fd41-0c40-4238-91c6-e52590fbff0b
-- title:
--   Lemma 3.11 — an enumerable downward-closed family C_t containing A ∩ B_t for every connected small cut
-- statement:
--   There are a constant $C$ and one deterministic machine that, given a graph $G$ on $n$ vertices, $k\ge0$ and a vertex set $B$ (the bag $B_t$), outputs within $C\cdot2^{Ck}(n+1)^C$ steps a list of a downward-closed family $\mathcal C_t\subseteq2^{B}$ with $|\mathcal C_t|\le C\cdot2^{Ck}(n+1)^C$, every member of size at most $2k$, such that $A\cap B\in\mathcal C_t$ for every $A\subseteq V(G)$ that is empty or induces a connected subgraph and has $|\delta_G(A)|\le k$ and $|A\cap B|\le2k$.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph → SimpleGraph (Fin n) with vertex set Fin n; reason: Lean convention; every such graph is isomorphic to one on Fin n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - generalization: B_t, a bag of the Section 3 decomposition → any vertex set B; reason: the proof (p. 27) uses only B_t as a vertex set (r_t is joined to B_t)
--   - reading: "connected A ⊆ V(G)" → A = ∅ or G[A] connected; reason: the paper's convention for A = ∅ is not stated; the stronger reading asks ∅ ∈ C_t, which (15) includes
--   - encoding: a family of size O*(2^{O(k)}), enumerated → the output encodeFamily L (order and repetition free); C_t = L.toFinset with card ≤ C·2^{Ck}(n+1)^C, the same C; reason: one constant for all O-terms of the lemma
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §3.4, p. 27, Lemma 3.11

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §3.4, p. 27, Lemma 3.11: one machine,
given `G`, `k` and a vertex set `B` (the bag `B_t`), enumerates within `C · 2^{C·k} · (n + 1)^C`
steps a downward-closed family `C_t ⊆ 2^B` of at most `C · 2^{C·k} · (n + 1)^C` sets, each of size
at most `2k`, such that `A ∩ B ∈ C_t` for every connected `A ⊆ V(G)` (or `A = ∅`) with
`|δ_G(A)| ≤ k` and `|A ∩ B| ≤ 2k`. -/
theorem lemma_3_11 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (B : Finset (Fin n)),
        ∃ L : List (Finset (Fin n)),
          HMBinPacking.OutputsWithin M (encodeInput G k ++ encodeSet B) (encodeFamily L)
            (stepBound C k n) ∧
          (∀ D ∈ L, D ⊆ B ∧ D.card ≤ 2 * k) ∧
          (∀ D ∈ L, ∀ D' : Finset (Fin n), D' ⊆ D → D' ∈ L) ∧
          L.toFinset.card ≤ stepBound C k n ∧
          ∀ A : Finset (Fin n), (A = ∅ ∨ (G.induce (A : Set (Fin n))).Connected) →
            cutSize G A ≤ k → (A ∩ B).card ≤ 2 * k → A ∩ B ∈ L := by sorry

end SingleExpBisect.Main
