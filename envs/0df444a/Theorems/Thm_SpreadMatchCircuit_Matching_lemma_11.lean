-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_lemma_11
-- name    : SpreadMatchCircuit.Matching.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:12.782476+00:00
-- url     : https://prove2.me/theorems/bd4e9347-3b82-4c51-8153-0e5d37429edd
-- title:
--   Lemma 11 — Algorithm 1 has few new positive errors: $p(X_1\in N^1_g)\le 2^{-t}$
-- statement:
--   Let $n=2N$, $1\le k\le N$, and let $X_1$ be a uniformly random matching with $k$ edges from $[n/2]$ to $[n]\setminus[n/2]$. Let $t,r$ be real numbers with $t\le k/100$ and
--
--   $$0<r\le\frac{n^2}{16k}.$$
--
--   Let $g=h_1\wedge h_2$ be an AND gate whose predecessors have families $M_{h_1},M_{h_2}$ of sets of at most $t$ edges, and let $M_g$ be the output of Algorithm 1. Then the new positive errors for $M_g$ satisfy
--
--   $$p_{X_1}\big(X_1\in N^1_g\big)\le 2^{-t}.$$
--
--   Together with Lemma 12 this bounds the error added at each gate of the circuit by the approximation, and a union bound over the gates gives the lower bound on circuit size.
--
--   **Formalization Note** The real exponent $2^{-t}$ is a real power. The objects are those of the `Approximator` definition.
--
--   Differences from the source:
--   - generalization: t and r fixed by Eq. (7) from q, k, n, η, α → any real t and r with t ≤ k/100 and 0 < r ≤ n²/(16k); reason: these are the two inequalities of Eq. (7) the bound depends on, and the parameters of Eq. (7) satisfy them.
--   - generalization: h₁, h₂ gates of a monotone circuit with families computed by the approximation → arbitrary Boolean functions with arbitrary families of sets of at most t edges; reason: the gates of the source are an instance.
--   - generalization: lexicographic order and any largest m → an arbitrary linear order, which also breaks ties among largest m; reason: the source's choices are instances.
--   - encoding: n even with sides [n/2] and its complement → vertices Fin (2N), sides of values below N and at least N; reason: the source's local construction needs n even, and the same instances result.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 12, Lemma 11 (Eqs. (6), (7), pp. 10–11; Algorithm 1, p. 12)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Approximator

namespace SpreadMatchCircuit.Matching

/-- Lemma 11, p. 12: `p(X₁ ∈ N¹_g) ≤ 2^{-t}` for `M_g` the output of Algorithm 1. -/
theorem lemma_11 (N k : ℕ) (hk₁ : 1 ≤ k) (hkN : k ≤ N) (t r : ℝ)
    (htk : t ≤ (k : ℝ) / 100)
    (hr₀ : 0 < r) (hr : r ≤ (2 * (N : ℝ)) ^ 2 / (16 * (k : ℝ)))
    (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N) (hG : G.SizeBounded t) :
    uniformProb (crossMatchings N k) (fun x => x ∈ G.newPos k (G.algorithm1 ord k r t))
      ≤ (2 : ℝ) ^ (-t) := by sorry

end SpreadMatchCircuit.Matching
