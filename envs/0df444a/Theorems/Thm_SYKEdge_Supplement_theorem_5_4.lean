-- Prove2me | Theorems.Thm_SYKEdge_Supplement_theorem_5_4
-- name    : SYKEdge.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:22:14.630309+00:00
-- url     : https://prove2.me/theorems/3d9a0c6a-0a39-44b3-adfb-5ef1869d8862
-- title:
--   Theorem 5.4 — subgaussian tails $\Pr(|\|H\|_{op}-\mathbb E\|H\|_{op}|\ge t)\le 2e^{-\Omega(nt^2)}$ for dense SYK
-- statement:
--   Let $n\ge k\ge2$ be even integers with $\alpha:=k^2/n<1/16$, and let $H=\binom nk^{-1/2}\sum_{S\in\binom{[n]}k}g_S\Gamma_S$ be the dense SYK Hamiltonian on Majorana operators of dimension $2^{n/2}$, with i.i.d. $N(0,1)$ disorder $(g_S)$. There is an absolute constant $c>0$ such that for every $t\ge0$
--   $$\Pr_g\Big(\big|\|H\|_{op}-\mathbb E_g\|H\|_{op}\big|\ge t\Big)\ \le\ 2\exp\!\big(-c\,n\,t^2\big).$$
--
--   The operator norm concentrates at scale $n^{-1/2}$ around its mean $\Theta(\sqrt n/k)$, so the bounds of Theorem 1.1 on $\mathbb E\|H\|_{op}$ hold for a typical disorder realization.
--
--   Differences from the source:
--   - encoding: an arbitrary irreducible unitary representation of the Majorana relations on C^N, N = 2^{n/2} (p.15, footnote 14) → every family γ : Fin n → Matrix ι ι ℂ with card ι = 2^{n/2} satisfying the three Majorana relations; reason: for even n the complex Clifford algebra on n generators is the full matrix algebra of size 2^{n/2}, so these families are exactly the irreducible representations; they are unitarily equivalent and share every spectral quantity
--   - encoding: Ω(nt²) in the exponent → c·n·t² with one absolute constant c > 0 quantified before n, k, the representation, the family and t; reason: the paper's Ω is an absolute constant (footnote 20, p.36)
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, Theorem 5.4, p.36 (PDF p.36)

import Mathlib
import Definitions.Def_SYKEdge_Hamiltonian
import Definitions.Def_SYKEdge_MatrixNorms

open Matrix MeasureTheory

namespace SYKEdge.Supplement

open SYKEdge

/-- **Theorem 5.4** (Subgaussian Tails for the Operator Norm), A. Basu, P. K. Kothari, S. Midha,
*Sharp Bounds on Ground State Energy of the SYK Model*, arXiv:2607.27185v2, p.36 (PDF p.36).

Let `n ⩾ k ⩾ 2` be even integers and `α := k²/n < 1/16`. For the dense SYK Hamiltonian
`H = (n choose k)^{−1/2} Σ_S g_S Γ_S` and every `t ⩾ 0`,
`Pr_g(|‖H‖_op − E_g ‖H‖_op| ⩾ t) ⩽ 2·exp(−Ω(n t²))`.

**Formalization Note.**
* `Ω(·)` is one absolute constant `c > 0` chosen before `n`, `k`, the representation and `t`
  (footnote 20, p.36): the bound is `2·exp(−c·n·t²)`.
* The probability is the standard Gaussian law `stdGauss (KSet n k)` of the disorder `(g_S)`, and
  `E_g ‖H‖_op` is the Bochner integral of `g ↦ ‖H(g)‖_op` against it (this map is integrable).
* Representations: any Majorana family `γ` on `ι` with `card ι = 2^{n/2}` (footnote 14). -/
theorem theorem_5_4 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n k : ℕ, Even n → Even k → 2 ≤ k → k ≤ n → (k : ℝ) ^ 2 / n < 1 / 16 →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = 2 ^ (n / 2) →
      ∀ γ : Fin n → Matrix ι ι ℂ, IsMajoranaFamily γ →
      ∀ t : ℝ, 0 ≤ t →
        stdGauss (KSet n k)
            {g | t ≤ |opNorm (sykDense γ g) - ∫ g', opNorm (sykDense γ g') ∂stdGauss (KSet n k)|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(c * n * t ^ 2))) := by sorry

end SYKEdge.Supplement
