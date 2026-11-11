-- Prove2me | Theorems.Thm_SemiStreamReach_Main_lemma_18
-- name    : SemiStreamReach.Main.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:53:49.226596+00:00
-- url     : https://prove2.me/theorems/45f444e1-3b3e-4f7f-bd33-1d6d1eb5f272
-- title:
--   Lemma 18 — exact shortest paths from $O(\log^2 n)$ calls of a $(1+c/\log n)$-approximate streaming algorithm
-- statement:
--   For any constant $a\ge1$ there is a constant $c=c(a)>0$ such that the following holds. Suppose that a streaming algorithm computes $(1+c/\log n)$-approximate distances from a source in directed graphs with $O(n)$ vertices and positive, polynomially bounded integer edge weights, using $\tilde O(n)$ space and $T_{\mathrm{apx}}$ passes. Then there is a streaming algorithm that computes an exact shortest-path tree (with the exact distances) in $n$-vertex directed graphs with integer edge weights in $\{0,1,\dots,n^a\}$, using $\tilde O(n)$ space and
--   $$O\big(T_{\mathrm{apx}}\log^2 n\big)$$
--   passes. If the approximate algorithm succeeds with high probability, then so does the exact algorithm.
--
--   Precisely: there are $c>0$, $K_0$, $b$ and $C$ such that (i) every program that, given the size parameter $N$ and a graph with at most $K_0N$ vertices and integer weights in $[1,(N+1)^b]$ (header $N,n',s+1$), outputs $(1+c/\log_2(N+2))$-approximate distances with failure probability $0$, in $A\,N(\log_2(N+2))^A$ bits and $T(N)$ passes on every coin tape, yields an exact program with failure probability $0$, $\tilde O(n)$ bits and $C\,T(n)\log_2^2(n+2)$ passes; and (ii) if for every $c'>0$ there is such an approximate program with failure probability at most $N^{-c'}$ and pass bound $T_{c'}$, then for every $c''>0$ there are $c'>0$ and an exact program with failure probability at most $n^{-c''}$, $\tilde O(n)$ bits and $C\,T_{c'}(n)\log_2^2(n+2)$ passes.
--
--   This is the streaming implementation of the reduction of Rozhoň, Haeupler, Martinsson et al.; it turns Theorem 17 into the exact result.
--
--   Differences from the source:
--   - reading: an approximate algorithm on graphs with O(n) vertices and positive, polynomially bounded integer weights, (1 + c/log n)-approximate → a program with header N, n', s + 1 (size parameter N): graphs with n' ≤ K0·N vertices and weights in [1, (N + 1)^b], accuracy 1 + c/log₂(N + 2); K0 and b chosen with c; reason: the reduction calls the approximate algorithm on graphs with up to n + 1 vertices at accuracy c/log n for the original n, so the algorithm must be told n; O(n) and the polynomial bound are constants of the reduction (existential, fixed with c); log₂(N + 2) avoids log 1 = 0 and changes c by at most a factor 2
--   - reading: "computes" (no probability) and "succeeds with high probability" → clause (i): failure probability 0 for both algorithms; clause (ii): if for every c' > 0 an approximate program fails with probability ≤ N^{−c'} (pass bound T_{c'}), then for every c'' > 0 an exact program fails with probability ≤ n^{−c''} (pass bound C·T_{c'}·log² for some c'); reason: §3 (p. 13) defines w.h.p. as ∀ c ∃ algorithm; the pass bound of the approximate algorithm may depend on its c'
--   - reading: "computes an exact shortest-path tree" → outputs the exact distances and a shortest-path tree (IsSSSPOutput); reason: the proof of Theorem 2 uses Lemma 18 to get "exact distances from s and a shortest-path tree", and Algorithm 6 outputs both
--   - reading: the resource bounds of a randomized algorithm that "with high probability computes …" → space and pass bounds on every coin tape; only correctness is probabilistic; reason: the sentence is ambiguous between bounds on every run and bounds w.h.p.; the every-run reading is the stronger one
--   - encoding: streaming algorithms, Õ(n) space, O(T_apx log² n) passes, word size O(log n) → DynBrooks programs with word size cw·ℓ(·); space ≤ A·N·(log₂(N+2))^A; passes ≤ C·T(n)·(log₂(n+2))² with C fixed with c; exact input header n, s + 1 and output layout of ExactSSSPSpec; reason: the paper names no instruction set; the constants are those hidden by Õ and O
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 16 (PDF 18), Lemma 18; proved in Appendix A, pp. 58-59 (PDF 60-61)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_StreamModel

open scoped ENNReal

namespace SemiStreamReach.Main

/-- Lemma 18 (Exact from approximate SSSP [RHM+23]), p. 16 (PDF 18); proved in Appendix A,
p. 58 (PDF 60). For every constant `a ≥ 1` there are a constant `c = c(a) > 0`, constants `K0`, `b`
(the `O(n)` vertex count and the polynomial weight bound of the approximate calls) and `C` (the
constant of `O(T_apx log² n)`) such that:
(i) for every approximate program `P` that, with size parameter `N`, computes
`(1 + c/log₂(N+2))`-approximate distances (failure probability `0`) on directed graphs with at most
`K0 · N` vertices and positive integer weights at most `(N + 1)^b`, in `A N (log₂(N+2))^A` bits and
`T N` passes on every coin tape, there is an exact program computing distances and a shortest-path
tree on `n`-vertex graphs with integer weights in `{0, …, n^a}` (failure probability `0`) in
`Õ(n)` bits and `C · T n · (log₂(n+2))²` passes on every coin tape;
(ii) if for every `c' > 0` such an approximate program exists with failure probability at most
`N^{−c'}` and pass bound `T c'`, then for every `c'' > 0` there are `c' > 0` and an exact program
with failure probability at most `n^{−c''}`, `Õ(n)` bits and `C · T c' n · (log₂(n+2))²` passes. -/
theorem lemma_18 :
    ∀ a : ℕ, 1 ≤ a → ∃ c : ℝ, 0 < c ∧ ∃ (K0 b : ℕ) (C : ℝ),
      (∀ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ) (T : ℕ → ℝ),
        ApproxOracleSpec P cw A T K0 b c (fun _ => 0) →
        ∃ (P' : DynBrooks.Program) (cw' : ℕ) (A' : ℝ),
          ExactSSSPSpec P' a cw' A' (fun n => C * T n * Real.logb 2 ((n : ℝ) + 2) ^ 2)
            (fun _ => 0)) ∧
      (∀ T : ℝ → ℕ → ℝ,
        (∀ c' : ℝ, 0 < c' → ∃ (P : DynBrooks.Program) (cw : ℕ) (A : ℝ),
          ApproxOracleSpec P cw A (T c') K0 b c (fun N => ENNReal.ofReal ((N : ℝ) ^ (-c')))) →
        ∀ c'' : ℝ, 0 < c'' → ∃ c' : ℝ, 0 < c' ∧
          ∃ (P' : DynBrooks.Program) (cw' : ℕ) (A' : ℝ),
            ExactSSSPSpec P' a cw' A' (fun n => C * T c' n * Real.logb 2 ((n : ℝ) + 2) ^ 2)
              (fun n => ENNReal.ofReal ((n : ℝ) ^ (-c'')))) := by sorry

end SemiStreamReach.Main
