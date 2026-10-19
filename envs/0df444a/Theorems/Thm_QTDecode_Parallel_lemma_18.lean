-- Prove2me | Theorems.Thm_QTDecode_Parallel_lemma_18
-- name    : QTDecode.Parallel.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:18.528553+00:00
-- url     : https://prove2.me/theorems/1954dd43-cd61-48c4-b30c-e7346d2bdadb
-- title:
--   Lemma 18, p. 26 — if the ε-sequential decoder converges, one parallel round removes ≥ (1/4)(1/4 − 3ε/2)|Z|
-- statement:
--   Let $\varepsilon\in(0,1/6)$, and let the current state of the mismatch decomposition, with mismatch $Z$, be such that the sequential decoder of parameter $\varepsilon$ converges from it: every run of Algorithm 2 with parameter $\varepsilon$ from this state that has not reached a zero mismatch can be extended by one more step. Then after one round of parallel decoding (Algorithm 3: the four parallel substeps on $V_{00},V_{01},V_{10},V_{11}$, every vertex flipping an admissible local codeword of maximum weight) the new mismatch $Z'$ satisfies
--   $$|Z'|\ \le\ |Z|-\frac14\Big(\frac14-\frac32\,\varepsilon\Big)|Z|.$$
--
--   Iterated, this gives the geometric decrease of the mismatch that makes the parallel decoder run in a logarithmic number of rounds (Theorem 20).
--
--   **Formalization Note** The lemma needs no hypothesis on the complex or the local codes: its proof is a counting argument comparing one parallel round with a converging sequential run. It is stated for arbitrary $G$, $A$, $B$, $C_A$, $C_B$, which is a stronger statement than the page's.
-- source:
--   Leverrier and Zémor, Decoding quantum Tanner codes, arXiv:2208.05537v3, p. 26, Lemma 18 (proof pp. 26–29, Claim 1 p. 27)

import Mathlib
import Definitions.Def_QTDecode_Parallel_Model

namespace QTDecode.Parallel

open QAlgorithms

/-- Lemma 18, p. 26. Let `ε ∈ (0, 1/6)` and let `s` be a state of the mismatch decomposition from
which the sequential decoder of parameter `ε` converges. Then after one round of parallel decoding
(Algorithm 3, substeps `V₀₀, V₀₁, V₁₀, V₁₁`) the weight of the mismatch has been reduced by at
least `(1/4)(1/4 − (3/2)ε)|Z|`, where `Z` is the mismatch at the start of the round. -/
theorem lemma_18 {G : Type} [Group G] [Fintype G] [DecidableEq G] {A B : Finset G}
    (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 6)
    (s s' : SeqDecState (G × A × B))
    (hconv : SeqConverges CA CB ε s) (hround : IsParRound CA CB s s') :
    (hammingNorm s'.Z : ℝ) ≤
      (hammingNorm s.Z : ℝ) - 1 / 4 * (1 / 4 - 3 / 2 * ε) * (hammingNorm s.Z : ℝ) := by sorry

end QTDecode.Parallel
