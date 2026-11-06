-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_6_8
-- name    : RandomLPIPM.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:50.946164+00:00
-- url     : https://prove2.me/theorems/1090c2fc-8cea-4d59-a0d0-3bba7c268465
-- title:
--   Theorem 6.8 — projection bound under the uniform subspace distribution
-- statement:
--   Let $c\in(0,1/2]$, $cn\le d\le(1-c)n$, and $A\in\mathbb R^{d\times n}$ with independent $\mathcal N(0,1)$ entries. Fix $\mu\in(0,1]$ and let $(x_\mu,s_\mu)$ be the $\mu$-central path point of LP(A). Conditioned on $(x_\mu,s_\mu)$, let $U\in\mathbb R^{d\times n}$ have orthonormal rows such that $\operatorname{im}[U^\top]$ is uniformly distributed among all $d$-dimensional subspaces of $\mathbb R^n$ that contain $s_\mu-\mathbf 1$ and are orthogonal to $x_\mu-\mathbf 1$. Then for every $q>0$ there are $K>0$ and $N_0$, depending only on $c$ and $q$, such that for $n\ge N_0$ and every $\mu\in(0,1]$, over $A$ and $U$,
--   $$\Pr\big[\|P(UX_\mu)\mathbf 1_n\|_\infty>K\log^{4.5}n\big]\le n^{-q}.$$
--
--   It is the projection bound in a model where the subspace is "freshly random" given the central path point; the transfer lemma of Section 7 moves it to the true law of $\ker A$ (Theorem 2.2).
--
--   Differences from the source:
--   - reading: w.h.p. over A and U, O(log^4.5 n) → ∀ q > 0 ∃ K > 0, N₀ (depending only on c, q) such that for n ≥ N₀ and every μ ∈ (0,1] the failure probability is ≤ n^(−q); reason: the paper's definition of w.h.p. (p.21) with the failure exponent arbitrary, as its proofs deliver (p.56, p.81)
--   - encoding: U drawn conditionally on (x_μ, s_μ) from the uniform law → (A, G) from the product of two independent standard Gaussian d×n laws, P(UX_μ) = refProj x_μ s_μ G; reason: drawing G independently of A and building U from (x_μ, s_μ) and G is the conditional sampling; refProj realizes the uniform law (proof of Lemma 6.10, p.49)
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
--   - encoding: (x_μ, s_μ) the solution of the central path equations → x_μ the log-barrier minimizer, s_μ = μ/x_μ; reason: equivalent by p.22
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 6.8, p.48

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_sMu
import Definitions.Def_RandomLPIPM_refProj
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 6.8 (Projection Bound under the Uniform Subspace Distribution).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 6.8,
p.48.

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries, `μ ∈ (0, 1]`
fixed and `(x_μ, s_μ)` the `μ`-central path point of LP(A). Conditioned on `(x_μ, s_μ)`, let `im[Uᵀ]`
be uniform among the `d`-dimensional subspaces containing `s_μ − 1` and orthogonal to `x_μ − 1`.
Then w.h.p. over `A` and `U`, `‖P(UX_μ)·1‖_∞ ≤ O(log^{4.5} n)`.

**Formalization Note.** `(A, G)` is drawn from the product of two independent standard Gaussian
laws, and `P(UX_μ)` is `refProj x_μ s_μ G`; drawing `G` independently of `A` and building `U` from
`(x_μ, s_μ)` and `G` is exactly the conditional sampling of `U` given `(x_μ, s_μ)`. "w.h.p." and `Ω(·)`/`O(·)` (p.21) are read as: for every exponent `q > 0` there are constants
depending only on `c` and `q` and a threshold `N₀` such that for `n ≥ N₀` the failure probability is
at most `n^{−q}`; `K` and
`N₀` are uniform in `μ ∈ (0, 1]`. -/
theorem theorem_6_8 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
    (GaussianMatrix.gaussianMatrix d n).prod (GaussianMatrix.gaussianMatrix d n)
      {p | K * Real.log n ^ (9 / 2 : ℝ) <
        ColumnRandLP.supNorm (refProj (xMu (Matrix.of p.1) μ) (sMu (Matrix.of p.1) μ) p.2 1)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
