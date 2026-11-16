-- Prove2me | Theorems.Thm_SYKEdge_Supplement_theorem_5_6
-- name    : SYKEdge.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:20.651199+00:00
-- url     : https://prove2.me/theorems/49baaa64-b9b6-46dc-b1fa-206f39ec2d50
-- title:
--   Theorem 5.6 — sparse SYK lower bound $\mathbb E\|H^{\mathcal H}\|_{op}\ge\sqrt{2/\alpha}\,(1-O(1)\max\{k^{-1/4},\alpha^2\})$ w.p. $1-O(1/\log n)$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha:=k^2/n<1/16$. Let $\mathcal H=(S_1,\dots,S_m)$ be a random $k$-uniform hypergraph with $m\ge 2^{Ck}n\log n$ hyperedges, for a large enough absolute constant $C>0$, and let $H=H^{\mathcal H}_{SYK}=m^{-1/2}\sum_{i=1}^m g_i\Gamma_{S_i}$ be the SYK Hamiltonian on $\mathcal H$ (as in Eq. (8)), on Majorana operators of dimension $2^{n/2}$, with i.i.d. $N(0,1)$ disorder. Then there is an absolute constant $C_1>0$ such that, with probability at least $1-C_1/\log n$ over $\mathcal H$,
--   $$\mathbb E_g\|H\|_{op}\ \ge\ \sqrt{\frac2\alpha}\Big(1-C_1\max\{k^{-1/4},\alpha^2\}\Big).$$
--
--   With Theorem 5.5 this pins the spectral edge of sparse SYK to $(1\pm o(1))\sqrt{2n}/k$ when $\omega(\log n)\le k\le o(\sqrt n)$ (Theorem 1.3).
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: H a random k-uniform hypergraph with m hyperedges, each sampled independently and uniformly from ([n] choose k), a multiset (p.37, footnote 6) → a tuple S : Fin m → KSet n k under the uniform probability hyperProb n k m (count of good tuples divided by (n choose k)^m); index i carries its own disorder g_i and |H| = m; reason: the uniform law on m-tuples is exactly the law of m i.i.d. uniform hyperedges; footnote 6 makes the disorder per index
--   - encoding: m ⩾ 2^{Ck} n log n where C > 0 is some sufficiently large absolute constant → ∃ C > 0 (first quantifier) with (2:ℝ)^(C·k)·n·Real.log n ≤ m; reason: a larger C only shrinks the set of admissible m, so 'for all sufficiently large C' and 'for some C' are the same statement; log is the natural logarithm
--   - encoding: with probability ⩾ 1 − O(1/log(n)) over the randomness of H → 1 − C₁/Real.log n ≤ hyperProb n k m (event), C₁ > 0 absolute; reason: the O(1/log n) is an explicit rate with an absolute constant (proof of Theorem 5.5, Markov at ζ = 1/(100 log n), p.38); footnote 20
--   - encoding: O(1) in the lower bound → the absolute constant C₁ > 0, quantified before n, k, m, the representation and the hypergraph; reason: the paper's constants are absolute (footnote 20, p.36)
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.6, p.40 (PDF p.40; proof pp.40–41)

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Supplement_RandomHypergraph

open Matrix MeasureTheory

namespace SYKEdge.Supplement

open SYKEdge

/-- **Theorem 5.6** (Operator Norm of the Sparse SYK: Lower Bound), A. Basu, P. K. Kothari,
S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*, arXiv:2607.27185v2, p.40
(PDF p.40).

Let `n ⩾ k ⩾ 2` be even integers with `α := k²/n < 1/16`, and let `H` be a random `k`-uniform
hypergraph with `m ⩾ 2^{Ck} n log n` hyperedges, `C > 0` a large enough absolute constant. Then
`E ‖H‖_op ⩾ √(2/α)·(1 − O(1)·max{k^{−1/4}, α²})` with probability `⩾ 1 − O(1/log n)` over `H`.

**Formalization Note.**
* `C`, the `O(1)` and the `O(1/log n)` are absolute constants chosen before `n`, `k`, `m`, the
  representation and the hypergraph (`C₁` serves for both `O`'s). "Large enough `C`" is `∃ C`.
* The hypergraph is a tuple `S : Fin m → KSet n k` with the uniform law `hyperProb`; index `i`
  carries its own disorder `g_i` (footnote 6); the Hamiltonian is `SYKEdge.syk γ (fun i => (S i).1) g`
  with `g ∼ stdGauss (Fin m)`. `k^{−1/4}` is the real power; `α² = (k²/n)²`.
* Representations: any Majorana family `γ` on `ι` with `card ι = 2^{n/2}` (footnote 14). -/
theorem theorem_5_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ n k m : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
        (2 : ℝ) ^ (C * k) * n * Real.log n ≤ m →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        1 - C₁ / Real.log n ≤ hyperProb n k m (fun S =>
          Real.sqrt (2 / ((k : ℝ) ^ 2 / n)) *
              (1 - C₁ * max ((k : ℝ) ^ (-(1 / 4 : ℝ))) (((k : ℝ) ^ 2 / n) ^ 2))
            ≤ ∫ g, opNorm (syk γ (fun i => (S i).1) g) ∂stdGauss (Fin m)) := by sorry

end SYKEdge.Supplement
