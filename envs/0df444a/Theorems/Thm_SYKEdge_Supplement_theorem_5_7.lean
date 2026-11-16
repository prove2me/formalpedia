-- Prove2me | Theorems.Thm_SYKEdge_Supplement_theorem_5_7
-- name    : SYKEdge.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:53.09546+00:00
-- url     : https://prove2.me/theorems/97b55548-2ebf-4caa-9b56-65a71a9065b9
-- title:
--   Theorem 5.7 — sparse SYK subgaussian tails $2e^{-\Omega(kt^2)}$ w.p. $1-O(1/\log n)$ over $\mathcal H$
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha:=k^2/n<1/16$. Let $\mathcal H=(S_1,\dots,S_m)$ be a random $k$-uniform hypergraph with $m\ge 2^{Ck}n\log n$ hyperedges, for a large enough absolute constant $C>0$, and let $H^{\mathcal H}_{SYK}=m^{-1/2}\sum_{i=1}^m g_i\Gamma_{S_i}$ be the SYK Hamiltonian on $\mathcal H$, on Majorana operators of dimension $2^{n/2}$, with i.i.d. $N(0,1)$ disorder. Then there are absolute constants $C_1,c>0$ such that, with probability at least $1-C_1/\log n$ over $\mathcal H$, for every $t\ge0$
--   $$\Pr_g\Big(\big|\|H^{\mathcal H}_{SYK}\|_{op}-\mathbb E_g\|H^{\mathcal H}_{SYK}\|_{op}\big|\ge t\Big)\ \le\ 2\exp\!\big(-c\,k\,t^2\big).$$
--
--   For a typical sparse hypergraph the operator norm concentrates at scale $k^{-1/2}$ around its mean.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: H a random k-uniform hypergraph with m hyperedges, each sampled independently and uniformly from ([n] choose k), a multiset (p.37, footnote 6) → a tuple S : Fin m → KSet n k under the uniform probability hyperProb n k m (count of good tuples divided by (n choose k)^m); index i carries its own disorder g_i and |H| = m; reason: the uniform law on m-tuples is exactly the law of m i.i.d. uniform hyperedges; footnote 6 makes the disorder per index
--   - encoding: m ⩾ 2^{Ck} n log n where C > 0 is some sufficiently large absolute constant → ∃ C > 0 (first quantifier) with (2:ℝ)^(C·k)·n·Real.log n ≤ m; reason: a larger C only shrinks the set of admissible m, so 'for all sufficiently large C' and 'for some C' are the same statement; log is the natural logarithm
--   - encoding: with probability ⩾ 1 − O(1/log(n)) over the randomness of H → 1 − C₁/Real.log n ≤ hyperProb n k m (event), C₁ > 0 absolute; reason: the O(1/log n) is an explicit rate with an absolute constant (proof of Theorem 5.5, Markov at ζ = 1/(100 log n), p.38); footnote 20
--   - encoding: Ω(kt²) in the exponent → c·k·t² with one absolute constant c > 0 quantified before n, k, m, the representation, the hypergraph and t; reason: the paper's Ω is an absolute constant (footnote 20, p.36)
--   - reading: for any t ⩾ 0 the tail bound holds, with probability ⩾ 1 − O(1/log(n)) over H → the event over H is 'for all t ≥ 0 the tail bound holds' (one good hypergraph serves every t); reason: the page does not say whether the good event may depend on t; the proof's event (bounds on ρ⁺, δ, q) does not, and this is the stronger reading
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.7, p.41 (PDF p.41)

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms
import Definitions.Def_SYKEdge_Supplement_RandomHypergraph

open Matrix MeasureTheory

namespace SYKEdge.Supplement

open SYKEdge

/-- **Theorem 5.7** (Subgaussian Tails for the Operator Norm for Sparse SYK), A. Basu,
P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, p.41 (PDF p.41).

Let `n ⩾ k ⩾ 2` be even integers with `α := k²/n < 1/16`, and let `H` be a random `k`-uniform
hypergraph with `m ⩾ 2^{Ck} n log n` hyperedges, `C > 0` a large enough absolute constant. Then for
any `t ⩾ 0`, `Pr_g(|‖H^H_SYK‖_op − E_g ‖H^H_SYK‖_op| ⩾ t) ⩽ 2·exp(−Ω(k t²))`, with probability
`⩾ 1 − O(1/log n)` over `H`.

**Formalization Note.**
* `C`, the `Ω(·)` (`c`) and the `O(1/log n)` (`C₁`) are absolute constants chosen before `n`, `k`,
  `m`, the representation, the hypergraph and `t`.
* The event over `H` is "for all `t ⩾ 0`, the tail bound holds": one good hypergraph serves every
  `t` (the stronger of the two readings of the page; the proof's event does not depend on `t`).
* The hypergraph is a tuple `S : Fin m → KSet n k` with the uniform law `hyperProb`; index `i`
  carries its own disorder `g_i` (footnote 6); `Pr_g` is `stdGauss (Fin m)` and `E_g` its integral.
* Representations: any Majorana family `γ` on `ι` with `card ι = 2^{n/2}` (footnote 14). -/
theorem theorem_5_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧
      ∀ n k m : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
        (2 : ℝ) ^ (C * k) * n * Real.log n ≤ m →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
        1 - C₁ / Real.log n ≤ hyperProb n k m (fun S =>
          ∀ t : ℝ, 0 ≤ t →
            stdGauss (Fin m)
                {g | t ≤ |opNorm (syk γ (fun i => (S i).1) g) -
                    ∫ g', opNorm (syk γ (fun i => (S i).1) g') ∂stdGauss (Fin m)|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(c * k * t ^ 2)))) := by sorry

end SYKEdge.Supplement
