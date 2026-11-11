-- Prove2me | Theorems.Thm_SemiStreamReach_Main_theorem_17
-- name    : SemiStreamReach.Main.theorem_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:54:00.716035+00:00
-- url     : https://prove2.me/theorems/bfc29a22-4f6d-4cd3-9342-c3e0c4810f18
-- title:
--   Theorem 17 — streaming $(1+\varepsilon)$-approximate SSSP in $\tilde O(n)$ space and $\tilde O(h_x/\varepsilon+x)$ passes; $n^{1/3+o(1)}$ for $x=\lceil n^{1/3}\rceil$
-- statement:
--   In the multi-pass streaming model on the randomized word RAM, let $G$ be a directed graph on $n$ vertices with positive integer edge weights of polynomial aspect ratio (weights in $[1,n^b]$), given as a stream in an arbitrary edge order, $s$ a source, $x\in[n]$ an integer and $\varepsilon$ an accuracy parameter ($0<\varepsilon\le1/2$, $1/\varepsilon\le(\log_2(n+2))^{c_0}$). There is a randomized streaming algorithm that computes $(1+\varepsilon)$-approximate distances from $s$,
--   $$\mathrm{dist}_G(s,v)\ \le\ \hat d(v)\ \le\ (1+\varepsilon)\,\mathrm{dist}_G(s,v)\quad\text{for all }v,$$
--   with high probability, using $\tilde O(n)$ space and $\tilde O(h_x/\varepsilon+x)$ passes, where $h_x$ is the hopbound (4). For $x=\lceil n^{1/3}\rceil$, this is $n^{1/3+o(1)}$ passes.
--
--   Precisely: there is $C_h>0$ such that for all $b$, $c_0$ and $c>0$ there are one program, $c_w$, $A$ and a function $f$ with $f(n)\to0$ such that on every input (header $n,s+1,x,\lceil1/\varepsilon\rceil$) and every coin tape the run uses at most $A\,n(\log_2(n+2))^A$ bits and halts within $A(h_x/\varepsilon+x)(\log_2(n+2))^A$ passes, and within $n^{1/3+f(n)}$ passes when $x=\lceil n^{1/3}\rceil$; its output is not a vector of $(1+\varepsilon)$-approximate distances from $s$ with probability at most $n^{-c}$.
--
--   Combined with the exact-from-approximate reduction (Lemma 18), this gives the main result.
--
--   Differences from the source:
--   - reading: the resource bounds of a randomized algorithm that "with high probability computes …" → space and pass bounds on every coin tape; only correctness is probabilistic; reason: the sentence is ambiguous between bounds on every run and bounds w.h.p.; the every-run reading is the stronger one
--   - reading: Õ(n), Õ(·), "with high probability", accuracy parameter ε with the standing assumptions ε ≤ 1/2 and 1/ε = O(log^{c0} n) → ∀ b c0, ∀ c > 0, ∃ program, cw, A: space ≤ A·n·(log₂(n+2))^A, passes ≤ A·(h_x/ε + x)·(log₂(n+2))^A, failure ≤ n^{−c}, for all 0 < ε ≤ 1/2 with 1/ε ≤ (log₂(n+2))^{c0}; C_h one constant fixed first; reason: §3 (p. 13) defines Õ and w.h.p.; c0 is arbitrary, so the constant of O(log^{c0} n) is absorbed by raising c0; C_h is the constant of (4), fixed before every lemma
--   - reading: positive edge weights of polynomial aspect ratio → integer weights in [1, n^b], for every b (the program depends on b); reason: the word RAM holds only integers; weights of polynomial aspect ratio are scaled to integers of polynomial size, as in the proof of Theorem 2, which applies Theorem 17 only to integer weights
--   - encoding: a streaming algorithm on a graph given as a stream, words of O(log n) bits, the parameters x and ε given to the algorithm → a DynBrooks.Program with word size cw·ℓ(n + ⌈1/ε⌉); one pass = header n, (s + 1,) x, ⌈1/ε⌉, edge words (u + 1, v + 1, w), end marker 0; same order every pass; space = bits of every cell ever written; reason: the paper names no instruction set; the algorithm sees ε through K = ⌈1/ε⌉ ≥ 1/ε, which loses nothing since a (1 + 1/K)-guarantee implies the (1 + ε) one
--   - encoding: log n and log log n in Õ and in h_x → log₂(n + 2) and log₂ log₂(n + 4); reason: defined and positive for every n ≥ 1; equal to the printed expressions up to factors tending to 1 or bounded constants absorbed by A and C_h
--   - reading: "For x = ⌈n^{1/3}⌉, this is n^{1/3+o(1)} passes" → a second clause: ∃ f with f(n) → 0, fixed with the program, such that for x = ⌈n^{1/3}⌉ the run halts within n^{1/3+f(n)} passes on every coin tape; reason: o(1) is a function of n tending to 0, fixed before the instance (§3)
--   - encoding: the computed estimates d̂(v) → 2n output words, a pair p, q per vertex meaning p/q (∞ when q = 0); reason: the estimates are rational or ∞; one encoding of the vector
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 15 (PDF 17), Theorem 17

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_ImplicitHopset
import Definitions.Def_SemiStreamReach_Main_StreamModel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Theorem 17, p. 15 (PDF 17). There is a constant `C_h > 0` (hopbound (4)) such that for every
weight exponent `b`, every `c0` and every `c > 0` there are one program `P`, a word-size constant
`cw`, a constant `A` and a function `f → 0` such that for every `n ≥ 1`, source `s`, `x ∈ [n]`,
`0 < ε ≤ 1/2` with `1/ε ≤ (log₂(n + 2))^{c0}`, directed graph on `Fin n` with integer weights in
`[1, n^b]` and edge order: on the stream with header `n, s + 1, x, ⌈1/ε⌉`, with word size
`cw · ℓ(n + ⌈1/ε⌉)`, on every coin tape the run uses at most `A n (log₂(n+2))^A` bits and halts
within `A (h_x/ε + x)(log₂(n+2))^A` passes, and within `n^{1/3 + f(n)}` passes when
`x = ⌈n^{1/3}⌉`; the coin tapes on which its output is not a vector of `(1 + ε)`-approximate
distances from `s` have probability at most `n^{−c}`. -/
theorem theorem_17 :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀ (b c0 : ℕ) (c : ℝ), 0 < c →
      ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ) (f : ℕ → ℝ),
        Filter.Tendsto f Filter.atTop (nhds 0) ∧
        ∀ (n : ℕ) (s : Fin n) (x : ℕ) (ε : ℝ) (E : Finset (Fin n × Fin n))
          (wt : Fin n × Fin n → ℕ) (σ : List (Fin n × Fin n)),
          1 ≤ n → 1 ≤ x → x ≤ n → 0 < ε → ε ≤ 1 / 2 →
          1 / ε ≤ Real.logb 2 ((n : ℝ) + 2) ^ c0 →
          (∀ e ∈ E, 1 ≤ wt e ∧ wt e ≤ n ^ b) → IsEdgeStream E σ →
          RunsWithin P (cw * ell (n + ⌈1 / ε⌉₊))
              ([n, s.val + 1, x, ⌈1 / ε⌉₊] ++ edgeWords wt σ ++ [0])
              (A * (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ A)
              (A * ((hopboundX Ch n x : ℝ) / ε + (x : ℝ)) * Real.logb 2 ((n : ℝ) + 2) ^ A) ∧
            (x = ⌈(n : ℝ) ^ ((1 : ℝ) / 3)⌉₊ →
              RunsWithin P (cw * ell (n + ⌈1 / ε⌉₊))
                ([n, s.val + 1, x, ⌈1 / ε⌉₊] ++ edgeWords wt σ ++ [0])
                (A * (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ A)
                ((n : ℝ) ^ ((1 : ℝ) / 3 + f n))) ∧
            DynBrooks.coinMeasure (cw * ell (n + ⌈1 / ε⌉₊))
                (failSet P (cw * ell (n + ⌈1 / ε⌉₊))
                  ([n, s.val + 1, x, ⌈1 / ε⌉₊] ++ edgeWords wt σ ++ [0])
                  (IsApproxOutput E wt s ε)) ≤
              ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end SemiStreamReach.Main
