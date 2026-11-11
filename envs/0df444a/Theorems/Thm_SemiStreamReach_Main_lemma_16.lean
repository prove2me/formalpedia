-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_16
-- name    : SemiStreamReach.Main.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:53:53.171629+00:00
-- url     : https://prove2.me/theorems/391f9f82-f087-496e-a8c4-3c11f8eec152
-- title:
--   Lemma 16 — streaming $(h_x,\varepsilon,x)$-implicit hopsets in $\tilde O(n)$ space and $\tilde O(h_x/\varepsilon+x)$ passes
-- statement:
--   In the multi-pass streaming model on the randomized word RAM, let $G$ be a directed graph on $n$ vertices with positive integer edge weights of polynomial aspect ratio (weights in $[1,n^b]$), given as a stream in an arbitrary edge order, let $x\in[n]$ be an integer and $\varepsilon$ an accuracy parameter ($0<\varepsilon\le1/2$ and $1/\varepsilon\le(\log_2(n+2))^{c_0}$, the standing assumptions of §3). Let
--   $$h_x=\Big\lceil \sqrt{n/x}\;n^{C_h/\log\log n}\Big\rceil$$
--   be the hopbound (4). There is a randomized streaming algorithm that, with high probability, computes an $(h_x,\varepsilon,x)$-implicit hopset of $G$ using $\tilde O(n)$ space and $\tilde O(h_x/\varepsilon+x)$ passes.
--
--   Precisely: there is $C_h>0$ such that for all $b$, $c_0$ and $c>0$ there are one program, a word-size constant $c_w$ and a constant $A$ such that on every such input (header $n,x,\lceil1/\varepsilon\rceil$), on every coin tape, the run uses at most $A\,n(\log_2(n+2))^A$ bits and halts within $A\,(h_x/\varepsilon+x)(\log_2(n+2))^A$ passes, and its output fails to encode an $(h_x,\varepsilon,x)$-implicit hopset of $G$ (with constant $A$ in Definition 7 (1)) with probability at most $n^{-c}$.
--
--   The implicit hopset is the paper's central object: it is stored in $\tilde O(n)$ space and makes approximate distances computable in few passes (Lemma 15).
--
--   Differences from the source:
--   - reading: the resource bounds of a randomized algorithm that "with high probability computes …" → space and pass bounds on every coin tape; only correctness is probabilistic; reason: the sentence is ambiguous between bounds on every run and bounds w.h.p.; the every-run reading is the stronger one
--   - reading: Õ(n), Õ(·), "with high probability", accuracy parameter ε with the standing assumptions ε ≤ 1/2 and 1/ε = O(log^{c0} n) → ∀ b c0, ∀ c > 0, ∃ program, cw, A: space ≤ A·n·(log₂(n+2))^A, passes ≤ A·(h_x/ε + x)·(log₂(n+2))^A, failure ≤ n^{−c}, for all 0 < ε ≤ 1/2 with 1/ε ≤ (log₂(n+2))^{c0}; C_h one constant fixed first; reason: §3 (p. 13) defines Õ and w.h.p.; c0 is arbitrary, so the constant of O(log^{c0} n) is absorbed by raising c0; C_h is the constant of (4), fixed before every lemma
--   - reading: positive edge weights of polynomial aspect ratio → integer weights in [1, n^b], for every b (the program depends on b); reason: the word RAM holds only integers; weights of polynomial aspect ratio are scaled to integers of polynomial size, as in the proof of Theorem 2, which applies Theorem 17 only to integer weights
--   - encoding: a streaming algorithm on a graph given as a stream, words of O(log n) bits, the parameters x and ε given to the algorithm → a DynBrooks.Program with word size cw·ℓ(n + ⌈1/ε⌉); one pass = header n, (s + 1,) x, ⌈1/ε⌉, edge words (u + 1, v + 1, w), end marker 0; same order every pass; space = bits of every cell ever written; reason: the paper names no instruction set; the algorithm sees ε through K = ⌈1/ε⌉ ≥ 1/ε, which loses nothing since a (1 + 1/K)-guarantee implies the (1 + ε) one
--   - encoding: log n and log log n in Õ and in h_x → log₂(n + 2) and log₂ log₂(n + 4); reason: defined and positive for every n ≥ 1; equal to the printed expressions up to factors tending to 1 or bounded constants absorbed by A and C_h
--   - encoding: the computed implicit hopset (H0, B) → output words: |L|, the H0 edges as (u + 1, v + 1, p, q) with weight p/q, q ≥ 1 (lightest weight per pair), the number of blocks, each block as its size and labels; checked with IsImplicitHopset for the input graph; reason: every weighted edge an algorithm can write is rational; this layout is one encoding of the pair
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 15 (PDF 17), Lemma 16; proved in §7, pp. 40-48 (PDF 42-50)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_ImplicitHopset
import Definitions.Def_SemiStreamReach_Main_StreamModel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 16 (Streaming implicit hopsets), p. 15 (PDF 17); proved in §7. There is a constant
`C_h > 0` (the constant of the hopbound (4)) such that for every weight exponent `b`, every `c0`
(standing assumption `1/ε = O(log^{c0} n)`, §3) and every `c > 0` there are one program `P`, a
word-size constant `cw` and a constant `A` such that for every `n ≥ 1`, every `x ∈ [n]`, every
`0 < ε ≤ 1/2` with `1/ε ≤ (log₂(n + 2))^{c0}`, every directed graph on `Fin n` with integer weights
in `[1, n^b]` and every edge order: on the stream with header `n, x, ⌈1/ε⌉`, with word size
`cw · ℓ(n + ⌈1/ε⌉)`, on every coin tape the run uses at most `A n (log₂(n+2))^A` bits and halts
within `A (h_x/ε + x) (log₂(n+2))^A` passes, and the coin tapes on which its output is not an
`(h_x, ε, x)`-implicit hopset of the input graph (with constant `A` in Definition 7 (1)) have
probability at most `n^{−c}`. -/
theorem lemma_16 :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀ (b c0 : ℕ) (c : ℝ), 0 < c →
      ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ),
        ∀ (n x : ℕ) (ε : ℝ) (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ)
          (σ : List (Fin n × Fin n)),
          1 ≤ n → 1 ≤ x → x ≤ n → 0 < ε → ε ≤ 1 / 2 →
          1 / ε ≤ Real.logb 2 ((n : ℝ) + 2) ^ c0 →
          (∀ e ∈ E, 1 ≤ wt e ∧ wt e ≤ n ^ b) → IsEdgeStream E σ →
          RunsWithin P (cw * ell (n + ⌈1 / ε⌉₊)) ([n, x, ⌈1 / ε⌉₊] ++ edgeWords wt σ ++ [0])
              (A * (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ A)
              (A * ((hopboundX Ch n x : ℝ) / ε + (x : ℝ)) * Real.logb 2 ((n : ℝ) + 2) ^ A) ∧
            DynBrooks.coinMeasure (cw * ell (n + ⌈1 / ε⌉₊))
                (failSet P (cw * ell (n + ⌈1 / ε⌉₊))
                  ([n, x, ⌈1 / ε⌉₊] ++ edgeWords wt σ ++ [0])
                  (IsImplicitHopsetOutput E wt (hopboundX Ch n x) ε x A)) ≤
              ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end SemiStreamReach.Main
