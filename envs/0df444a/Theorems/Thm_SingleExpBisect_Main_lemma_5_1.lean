-- Prove2me | Theorems.Thm_SingleExpBisect_Main_lemma_5_1
-- name    : SingleExpBisect.Main.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:41:53.003214+00:00
-- url     : https://prove2.me/theorems/7ce4a175-ea96-4305-808b-aa03ffc638aa
-- title:
--   Lemma 5.1 — shrink a breakable bag keeping X and adhesion ≤ 2k, or certify (2k,k)-edge-unbreakability
-- statement:
--   Let $H$ be a graph on $n$ vertices, $k\ge0$, and $X\subseteq B\subseteq V(H)$ with $|X|\le2k+1$ and $\mathrm{adh}_H(B)\le2k$. There are a constant $C$ and one deterministic machine that, on input $(H,k,X,B)$, within $C\cdot2^{Ck}\cdot(n+1)^C$ steps either outputs a set $B'$ with $X\subseteq B'$, $|B'|<|B|$ and $\mathrm{adh}_H(B')\le2k$, or reports that $B$ is $(2k,k)$-edge-unbreakable in $H$, and the report is then correct.
--
--   Differences from the source:
--   - encoding: a finite simple undirected graph → SimpleGraph (Fin n) with vertex set Fin n; reason: Lean convention; every such graph is isomorphic to one on Fin n
--   - encoding: running time O*(·) on an unspecified machine → one deterministic TM2 machine (published OutputsWithin) and one constant C, both chosen before the instance, with the stated step bound in n = |V| and the parameter; reason: the paper names no machine model; O* suppresses factors polynomial in the input size, whose length is polynomial in n up to a log-of-parameter term absorbed by the exponential factor
--   - encoding: "either find B′ … or certify that B is (2k,k)-edge-unbreakable" → the output is true :: encodeSet B′ (with the three properties) or [false] (and then B is (2k,k)-edge-unbreakable in H); reason: a fixed two-way output format for the two outcomes
-- source:
--   Kumabe, Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New Unbreakable Decomposition, arXiv:2611.05982 (October 2026 version; PDF SHA256 6530ce94…6b76541), §5, p. 32, Lemma 5.1

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_SingleExpBisect_Main_Graphs
import Definitions.Def_SingleExpBisect_Main_Encodings

open scoped Classical

namespace SingleExpBisect.Main

open MinBisectFPT

/-- Kumabe, *Single-Exponential FPT Algorithms for Minimum Bisection and Matching Cut via a New
Unbreakable Decomposition*, arXiv:2611.05982 (October 2026), §5, p. 32, Lemma 5.1: for
`X ⊆ B ⊆ V(H)` with `|X| ≤ 2k + 1` and `adh_H(B) ≤ 2k`, one machine, within
`C · 2^{C·k} · (n + 1)^C` steps, either outputs `true` followed by a set `B′` with `X ⊆ B′`,
`|B′| < |B|` and `adh_H(B′) ≤ 2k`, or outputs `false` and then `B` is (2k, k)-edge-unbreakable
in `H`. -/
theorem lemma_5_1 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (k : ℕ) (X B : Finset (Fin n)),
        X ⊆ B → X.card ≤ 2 * k + 1 → adh H B ≤ 2 * k →
        ∃ out : List Bool,
          HMBinPacking.OutputsWithin M (encodeInput H k ++ encodeSet X ++ encodeSet B) out
            (stepBound C k n) ∧
          ((out = [false] ∧ IsEdgeUnbreakable H Finset.univ B (2 * k) k) ∨
            ∃ B' : Finset (Fin n), out = true :: encodeSet B' ∧ X ⊆ B' ∧ B'.card < B.card ∧
              adh H B' ≤ 2 * k) := by sorry

end SingleExpBisect.Main
