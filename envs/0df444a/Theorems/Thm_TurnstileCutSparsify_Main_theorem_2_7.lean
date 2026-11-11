-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_theorem_2_7
-- name    : TurnstileCutSparsify.Main.theorem_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:41:25.864107+00:00
-- url     : https://prove2.me/theorems/71efe969-a224-4bad-859b-0f818e9dcda5
-- title:
--   Theorem 2.7 — (1+ε₀)-approximate Gomory–Hu tree in Õ(m_H poly(1/ε₀)) time with high probability ([LNPS23, Theorem 1.2])
-- statement:
--   For every $\varepsilon_0>0$, there is a randomized algorithm that, given a connected undirected graph $H$ with $m_H$ edges and positive weights whose ratio is polynomially bounded, computes a $(1+\varepsilon_0)$-approximate Gomory–Hu tree of $H$ in $\tilde O(m_H\,\mathrm{poly}(1/\varepsilon_0))$ time with high probability, that is, with probability at least $1-n_H^{-c}$ for a constant $c>0$ fixed in advance ($n_H$ the number of vertices of $H$).
--
--   Differences from the source:
--   - reading: positive weights whose ratio is polynomially bounded → positive integer weights at most n_H^{c₁}, for a constant c₁ fixed in advance (input as words); reason: on the word RAM the weights are O(log n_H)-bit numbers; this is the case Lemma 7.2 uses (integer weights between 1 and n^{O(1)}, p. 29)
--   - encoding: Õ(m_H poly(1/ε₀)) time; "with high probability" = 1 − n_H^{−c} → ∀ c₁ c : ℕ ∃ C K Cw a, ∀ ε₀ > 0 ∃ program: time T ≤ C m_H (1 + 1/ε₀)^K (log₂ n_H)^a and probability ≥ 1 − n_H^{−c}; reason: C, K, a do not depend on ε₀, so the poly(1/ε₀) dependence is real; natural c covers every real c > 0
--   - encoding: a connected graph H (n_H ≥ 1) → n_H ≥ 2; H : Pair n_H → ℕ connected; input n_H, m_H and any listing of its edges, then the random words; output a spanning tree in parent form with rational weights (decodeRatForest); reason: a one-vertex graph has only the empty tree and makes Õ(m_H) = Õ(0) degenerate (nondegeneracy only)
--   - generalization: a randomized algorithm on the word RAM with Θ(log n_H)-bit words → one program (for each ε₀) correct and within the time bound for every word size w ≥ Cw log₂ n_H; reason: larger words never hurt a word-RAM algorithm; the source's word size is an instance
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Theorem 2.7, p. 11

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Theorem 2.7** ([LNPS23, Theorem 1.2]; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 11).
For every `ε₀ > 0`, there is a randomized algorithm that, given a connected undirected graph `H` with
`m_H` edges and positive weights whose ratio is polynomially bounded (positive integer weights at
most `n_H^{c₁}`), computes a `(1 + ε₀)`-approximate Gomory–Hu tree of `H` in `Õ(m_H poly(1/ε₀))`
time with high probability (at least `1 − n_H^{−c}`, for a constant `c > 0` fixed in advance).
The algorithm is one word-RAM program for all inputs and all word sizes `w ≥ C_w log₂ n_H`; its
input is `n_H, m_H` and the edge list, followed by its random words. -/
theorem theorem_2_7 :
    ∀ c₁ c : ℕ, ∃ (C K Cw : ℝ) (a : ℕ), ∀ ε₀ : ℝ, 0 < ε₀ → ∃ P : Program,
    ∀ nH : ℕ, 2 ≤ nH → ∀ w : ℕ, Cw * Real.logb 2 nH ≤ w →
    ∀ H : Pair nH → ℕ, (supportGraph (toR H)).Connected → (∀ e, (H e : ℝ) ≤ (nH : ℝ) ^ c₁) →
    ∀ L : List (Pair nH × ℕ), IsEdgeListing H L →
    ∃ (Scells Lr T : ℕ),
      (T : ℝ) ≤ C * L.length * (1 + 1 / ε₀) ^ K * Real.logb 2 nH ^ a ∧
      (∀ r : Fin Lr → Fin (2 ^ w), ∃ m Tr,
        randRun P w Scells T (nH :: L.length :: encEdges L) r = some m ∧
          decodeRatForest nH m = some Tr) ∧
      1 - (nH : ℝ) ^ (-(c : ℝ)) ≤ prob (fun r : Fin Lr → Fin (2 ^ w) => ∃ m Tr,
        randRun P w Scells T (nH :: L.length :: encEdges L) r = some m ∧
          decodeRatForest nH m = some Tr ∧ IsApproxGH ε₀ (toR H) Tr.toForest) := by sorry

end TurnstileCutSparsify.Main
