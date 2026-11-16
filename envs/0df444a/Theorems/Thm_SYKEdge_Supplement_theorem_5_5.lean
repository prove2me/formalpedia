-- Prove2me | Theorems.Thm_SYKEdge_Supplement_theorem_5_5
-- name    : SYKEdge.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:22:46.727169+00:00
-- url     : https://prove2.me/theorems/e18633f2-ff02-4885-bc32-6bc272fc8ebf
-- title:
--   Theorem 5.5 — sparse SYK upper bound $\mathbb E\|H^{\mathcal H}\|_{op}\le\sqrt{2/\alpha}\,(1+O(\sqrt{\alpha+e^{-\Omega(k)}}))$ w.p. $1-O(1/\log n)$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha:=k^2/n<1/16$. Let $\mathcal H=(S_1,\dots,S_m)$ be a random $k$-uniform hypergraph with $m\ge 2^{Ck}n\log n$ hyperedges, where $C>0$ is a sufficiently large absolute constant, and let
--   $$H^{\mathcal H}_{SYK}:=\frac1{\sqrt{|\mathcal H|}}\sum_{S\in\mathcal H}g_S\Gamma_S$$
--   be the SYK Hamiltonian on $\mathcal H$, on Majorana operators of dimension $2^{n/2}$, with an independent $N(0,1)$ disorder variable for each of the $m$ hyperedges. Then there are absolute constants $C_1,c,A>0$ such that, with probability at least $1-C_1/\log n$ over $\mathcal H$,
--
--   1. $$\mathbb E_g\|H^{\mathcal H}_{SYK}\|_{op}\ \le\ \sqrt{\frac2\alpha}\Big(1+C_1\sqrt{\alpha+e^{-ck}}\Big)=\frac{\sqrt{2n}}k\Big(1+C_1\sqrt{\tfrac{k^2}n+e^{-ck}}\Big);$$
--   2. in particular, if $k\ge A\log n$, then $\mathbb E_g\|H^{\mathcal H}_{SYK}\|_{op}\le\sqrt{2n}/k+C_1$.
--
--   Sparse SYK with only $2^{O(k)}n\log n$ terms thus has the same spectral edge $\sqrt{2n}/k$ as the dense model with $\binom nk$ terms, to first order.
--
--   **Formalization Note** Both clauses hold on one event of $\mathcal H$. The probability over $\mathcal H$ is the uniform probability on $m$-tuples of $k$-subsets.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: H a random k-uniform hypergraph with m hyperedges, each sampled independently and uniformly from ([n] choose k), a multiset (p.37, footnote 6) → a tuple S : Fin m → KSet n k under the uniform probability hyperProb n k m (count of good tuples divided by (n choose k)^m); index i carries its own disorder g_i and |H| = m; reason: the uniform law on m-tuples is exactly the law of m i.i.d. uniform hyperedges; footnote 6 makes the disorder per index
--   - encoding: m ⩾ 2^{Ck} n log n where C > 0 is some sufficiently large absolute constant → ∃ C > 0 (first quantifier) with (2:ℝ)^(C·k)·n·Real.log n ≤ m; reason: a larger C only shrinks the set of admissible m, so 'for all sufficiently large C' and 'for some C' are the same statement; log is the natural logarithm
--   - encoding: with probability ⩾ 1 − O(1/log(n)) over the randomness of H → 1 − C₁/Real.log n ≤ hyperProb n k m (event), C₁ > 0 absolute; reason: the O(1/log n) is an explicit rate with an absolute constant (proof of Theorem 5.5, Markov at ζ = 1/(100 log n), p.38); footnote 20
--   - encoding: the O(·) in the bound, the Ω(k) in e^{−Ω(k)} and the O(1) of the 'in particular' clause → absolute constants C₁ (all O's) and c > 0 (the Ω), quantified before n, k, m, the representation and the hypergraph; reason: the paper's constants are absolute (footnote 20, p.36)
--   - reading: In particular if k ⩾ ω(log(n)) then E‖H^H_SYK‖_op ⩽ √(2n)/k + O(1) → ∃ A > 0 such that A·log n ≤ k implies E‖H^H_SYK‖_op ≤ √(2n)/k + C₁, on the same event of probability ⩾ 1 − C₁/log n as the main bound; reason: the sequence-free form of the asymptotic hypothesis; it implies the asymptotic reading and follows from the main bound since √(2n)/k·e^{−ck/2} ≤ 1 once k ≥ A·log n
--   - encoding: the chain √(2/α)·(1 + O(√(α + e^{−Ω(k)}))) = (√(2n)/k)·(1 + O(√(k²/n + e^{−Ω(k)}))) → only the first form, with α written as k²/n; reason: the two forms are equal for α = k²/n
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.5, p.37 (PDF p.37; proof pp.37–40)

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Supplement_RandomHypergraph

open Matrix MeasureTheory

namespace SYKEdge.Supplement

open SYKEdge

/-- **Theorem 5.5** (Operator Norm of the Sparse SYK: Upper Bound), A. Basu, P. K. Kothari,
S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*, arXiv:2607.27185v2, p.37
(PDF p.37).

Let `n ⩾ k ⩾ 2` be even integers with `α := k²/n < 1/16`, and let `H = (S₁, …, S_m)` be a random
`k`-uniform hypergraph with `m ⩾ 2^{Ck} n log n` hyperedges, `C > 0` a sufficiently large absolute
constant. For `H^H_SYK = |H|^{−1/2} Σ_i g_i Γ_{S_i}`, with probability `⩾ 1 − O(1/log n)` over `H`,
`E_g ‖H^H_SYK‖_op ⩽ √(2/α)·(1 + O(√(α + e^{−Ω(k)})))`; in particular, if `k ⩾ ω(log n)` then
`E_g ‖H^H_SYK‖_op ⩽ √(2n)/k + O(1)`.

**Formalization Note.**
* `C`, every `O(·)`, the `Ω(k)` and the `O(1/log n)` are absolute constants chosen before `n`, `k`,
  `m`, the representation and the hypergraph: `C` (hyperedge count), `C₁` (all `O`'s and the
  failure rate `C₁/log n`), `c` (the `Ω(k)`), `A` (the threshold of the "in particular" clause).
  "Sufficiently large `C`" is `∃ C`: a larger `C` only shrinks the set of admissible `m`.
* The hypergraph is a tuple `S : Fin m → KSet n k` with the uniform law `hyperProb` (i.i.d. uniform
  hyperedges, repetitions allowed); index `i` carries its own disorder `g_i` (footnote 6), so the
  Hamiltonian is `SYKEdge.syk γ (fun i => (S i).1) g` with `g ∼ stdGauss (Fin m)`, `|H| = m`.
* "`k ⩾ ω(log n)`" is stated uniformly: `k ⩾ A·log n`. Both bounds hold on one event of
  probability `⩾ 1 − C₁/log n`. `log` is the natural logarithm; `2^{Ck}` is the real power.
* Representations: any Majorana family `γ` on `ι` with `card ι = 2^{n/2}` (footnote 14). -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∃ C₁ c A : ℝ, 0 < C₁ ∧ 0 < c ∧ 0 < A ∧
      ∀ n k m : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
        (2 : ℝ) ^ (C * k) * n * Real.log n ≤ m →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        1 - C₁ / Real.log n ≤ hyperProb n k m (fun S =>
          (∫ g, opNorm (syk γ (fun i => (S i).1) g) ∂stdGauss (Fin m) ≤
              Real.sqrt (2 / ((k : ℝ) ^ 2 / n)) *
                (1 + C₁ * Real.sqrt ((k : ℝ) ^ 2 / n + Real.exp (-(c * k))))) ∧
          (A * Real.log n ≤ k →
            ∫ g, opNorm (syk γ (fun i => (S i).1) g) ∂stdGauss (Fin m) ≤
              Real.sqrt (2 * n) / k + C₁)) := by sorry

end SYKEdge.Supplement
