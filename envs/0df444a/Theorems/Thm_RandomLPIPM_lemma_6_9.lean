-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_6_9
-- name    : RandomLPIPM.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:25.849542+00:00
-- url     : https://prove2.me/theorems/1cd8f144-7087-41f7-8fe4-4f7975950e43
-- title:
--   Lemma 6.9 — projection bound with norm bounds: $\|P(UX)\mathbf 1\|_\infty=O(\log^{4.5}n)$ w.h.p.
-- statement:
--   Let $c\in(0,1/2]$ and $cn\le d\le(1-c)n$. Let $x,s\in\mathbb R^n_{>0}$ be fixed with $\langle x-\mathbf 1,s-\mathbf 1\rangle=0$ and, for some $\alpha\in(0,1]$, the norm bounds (64):
--   $$\|x-\mathbf 1\|_2,\ \|s-\mathbf 1\|_2,\ \|X(s-\mathbf 1)\|_2\ \ge c_1\alpha\sqrt n,\qquad \|x-\mathbf 1\|_\infty,\ \|s-\mathbf 1\|_\infty,\ \|X(s-\mathbf 1)\|_\infty\ \le c_2\alpha\sqrt{\log n},$$
--   with fixed constants $c_1,c_2>0$. Let $U\in\mathbb R^{d\times n}$ have orthonormal rows with $\operatorname{im}[U^\top]$ uniformly distributed among the $d$-dimensional subspaces of $\mathbb R^n$ that contain $s-\mathbf 1$ and are orthogonal to $x-\mathbf 1$. Then for every $q>0$ there are $K>0$ and $N_0$, depending only on $c,c_1,c_2,q$, such that for $n\ge N_0$
--   $$\Pr\big[\|P(UX)\mathbf 1_n\|_\infty>K\log^{4.5}n\big]\le n^{-q}.$$
--
--   This is the deterministic-input version of the projection bound: once the central path point is known to be balanced, a uniformly random compatible subspace gives a small $\ell_\infty$ projection of $\mathbf 1$.
--
--   Differences from the source:
--   - reading: Ω(α√n) and O(α√log n) in (64); w.h.p., O(log^4.5 n) → fixed constants c₁, c₂ > 0 in (64); ∀ q > 0 ∃ K > 0, N₀ (depending only on c, c₁, c₂, q) with failure probability ≤ n^(−q) for n ≥ N₀; reason: the constants hidden in (64) are fixed before n; w.h.p. as on p.21
--   - encoding: U with im[Uᵀ] uniform among d-subspaces containing s − 1 and orthogonal to x − 1; P(UX) → refProj x s G with G a standard Gaussian d×n matrix (span of s − 1 and the projected Gaussian rows, multiplied by X); reason: Mathlib has no Haar measure on Grassmannians; by rotation invariance this construction has the uniform law (proof of Lemma 6.10, p.49), and P(UX) depends only on im[Uᵀ]
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.9, p.48

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_refProj
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Lemma 6.9 (Projection Bound with Norm Bounds).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.9, p.48.

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, and `x, s ∈ ℝⁿ_{>0}` fixed with `⟨x − 1, s − 1⟩ = 0` and, for
some `α ∈ (0, 1]`, the norm bounds (64):
`‖x − 1‖₂, ‖s − 1‖₂, ‖X(s − 1)‖₂ ≥ Ω(α√n)` and `‖x − 1‖_∞, ‖s − 1‖_∞, ‖X(s − 1)‖_∞ ≤ O(α√(log n))`.
Let `im[Uᵀ]` be uniform among the `d`-dimensional subspaces containing `s − 1` and orthogonal to
`x − 1`. Then w.h.p. `‖P(UX)·1‖_∞ ≤ O(log^{4.5} n)`.

**Formalization Note.** The constants of (64) are fixed as `c₁` (for `Ω`) and `c₂` (for `O`); "w.h.p." and `Ω(·)`/`O(·)` (p.21) are read as: for every exponent `q > 0` there are constants
depending only on `c` and `q` and a threshold `N₀` such that for `n ≥ N₀` the failure probability is
at most `n^{−q}`,
with `K` and `N₀` depending only on `c, c₁, c₂, q` (not on `x, s, α, d`). `P(UX)` under the uniform
subspace law is `refProj x s G` with `G` standard Gaussian (see `refProj`). -/
theorem lemma_6_9 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ → ∀ q : ℝ, 0 < q →
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ x s : Fin n → ℝ, (∀ i, 0 < x i) → (∀ i, 0 < s i) → (x - 1) ⬝ᵥ (s - 1) = 0 →
    ∀ α : ℝ, 0 < α → α ≤ 1 →
    c₁ * (α * Real.sqrt n) ≤ ColumnRandLP.l2Norm (x - 1) →
    c₁ * (α * Real.sqrt n) ≤ ColumnRandLP.l2Norm (s - 1) →
    c₁ * (α * Real.sqrt n) ≤ ColumnRandLP.l2Norm (x * (s - 1)) →
    ColumnRandLP.supNorm (x - 1) ≤ c₂ * (α * Real.sqrt (Real.log n)) →
    ColumnRandLP.supNorm (s - 1) ≤ c₂ * (α * Real.sqrt (Real.log n)) →
    ColumnRandLP.supNorm (x * (s - 1)) ≤ c₂ * (α * Real.sqrt (Real.log n)) →
    GaussianMatrix.gaussianMatrix d n {G | K * Real.log n ^ (9 / 2 : ℝ) < ColumnRandLP.supNorm (refProj x s G 1)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
