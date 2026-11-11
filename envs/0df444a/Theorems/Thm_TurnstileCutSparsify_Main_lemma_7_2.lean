-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_7_2
-- name    : TurnstileCutSparsify.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:06.168951+00:00
-- url     : https://prove2.me/theorems/964106cb-c25b-4d33-b816-e4ea3c5e9549
-- title:
--   Lemma 7.2 — query forest: one call of Theorem 2.7 on the hub-padded graph gives a 1.01-approximate Gomory–Hu tree of every nontrivial component with exact fundamental-cut weights
-- statement:
--   Let $H$ be a graph on $V$ with $m_H$ edges, whose weights are positive multiples of $2^{-\mu}$ and at most $n^{O(1)}$, where $2^\mu\le n^{O(1)}$, and let $\delta_1>0$ with $\delta_1^{-1}\le n^{O(1)}$. Let $C_1,\dots,C_t$ be the connected components of $H$ with at least two vertices. There is a randomized algorithm that uses $\tilde O(m_H+n)$ time and space and, with probability at least $1-\delta_1$, returns for each $a\in[t]$ a tree $T_a$ on $C_a$, rooted at $r_a=\min C_a$, with edge weights $\tau_q$ such that, where the fundamental cut $S_q$ of a tree edge $q$ is the side of $T_a-q$ that contains $r_a$:
--   1. $\tau_q=w_H(S_q,V\setminus S_q)>0$ for every tree edge $q$;
--   2. $\lambda_H(u,v)\le\tau_q\le1.01\,\lambda_H(u,v)$ for all distinct $u,v\in C_a$ and every minimum-weight edge $q$ on the $u$–$v$ path of $T_a$.
--
--   Differences from the source:
--   - encoding: n^{O(1)} bounds on the weights, 2^µ and δ₁⁻¹; Õ(m_H + n) time and space → ∀ c ∃ C Cw a: weights k_e 2^{−µ} ≤ n^c, 2^µ ≤ n^c, δ₁⁻¹ ≤ n^c; time T and cells S ≤ C (m_H + n)(log₂ n)^a; reason: the BRIEF.json quantifier order; space counted in words (the paper: "the space is bounded by the time")
--   - encoding: "returns for each a a tree T_a on C_a" → one rooted forest in parent form (decodeRatForest) satisfying IsQueryForest: its trees are the components with ≥ 2 vertices rooted at their minimum, and every vertex of a one-vertex component is a childless root; reason: the singleton roots carry no tree edge and change no fundamental cut
--   - generalization: an algorithm that may use δ₁ → one program, not given δ₁, that succeeds with probability ≥ 1 − δ₁ for every δ₁ with δ₁⁻¹ ≤ n^c, for every word size w ≥ Cw log₂ n; reason: the guarantee for every admissible δ₁ and every larger word size implies the source's
--   - encoding: vertices V = [n]; coordinates = the N unordered pairs; graphs G = (V, E, w) → vertices Fin n (0-based); Pair n = {(u, v) : u < v}; a graph is a weight function on Pair n (E = pairs of positive weight); reason: same graphs; the canonical pair order is not needed by the statement
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 7.2, p. 29

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Lemma 7.2** (Query forest; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 29).
Let `H` be a graph on `V` with `m_H` edges, whose weights are positive multiples of `2^{−µ}` and at
most `n^{O(1)}`, where `2^µ ≤ n^{O(1)}`, and let `δ₁ > 0` with `δ₁⁻¹ ≤ n^{O(1)}`. Let `C_1, …, C_t` be
the connected components of `H` with at least two vertices. There is a randomized algorithm that uses
`Õ(m_H + n)` time and space and, with probability at least `1 − δ₁`, returns for each `a` a tree
`T_a` on `C_a`, rooted at `r_a = min C_a`, with edge weights `τ_q` such that, with `S_q` the side of
`T_a − q` containing `r_a`: (1) `τ_q = w_H(S_q, V \ S_q) > 0` for every tree edge `q`; (2)
`λ_H(u, v) ≤ τ_q ≤ 1.01 λ_H(u, v)` for all distinct `u, v ∈ C_a` and every minimum-weight edge `q`
on the `u`–`v` path of `T_a` (`IsQueryForest`). The algorithm is one word-RAM program for all inputs
and all word sizes `w ≥ C_w log₂ n`; its input is `n, µ, m_H` and the edge list (each weight `k_e`
standing for `k_e 2^{−µ}`), followed by its random words. -/
theorem lemma_7_2 :
    ∀ c : ℕ, ∃ (C Cw : ℝ) (a : ℕ) (P : Program),
    ∀ n : ℕ, 2 ≤ n → ∀ w : ℕ, Cw * Real.logb 2 n ≤ w →
    ∀ (μ : ℕ) (k : Pair n → ℕ), (2 : ℝ) ^ μ ≤ (n : ℝ) ^ c →
      (∀ e, (k e : ℝ) / 2 ^ μ ≤ (n : ℝ) ^ c) →
    ∀ L : List (Pair n × ℕ), IsEdgeListing k L →
    ∃ (Scells Lr T : ℕ),
      (T : ℝ) ≤ C * (L.length + n) * Real.logb 2 n ^ a ∧
      (Scells : ℝ) ≤ C * (L.length + n) * Real.logb 2 n ^ a ∧
      (∀ r : Fin Lr → Fin (2 ^ w), ∃ m F,
        randRun P w Scells T (n :: μ :: L.length :: encEdges L) r = some m ∧
          decodeRatForest n m = some F) ∧
      ∀ δ₁ : ℝ, 0 < δ₁ → δ₁⁻¹ ≤ (n : ℝ) ^ c →
        1 - δ₁ ≤ prob (fun r : Fin Lr → Fin (2 ^ w) => ∃ m F,
          randRun P w Scells T (n :: μ :: L.length :: encEdges L) r = some m ∧
            decodeRatForest n m = some F ∧
            IsQueryForest (fun e => (k e : ℝ) / 2 ^ μ) F.toForest) := by sorry

end TurnstileCutSparsify.Main
