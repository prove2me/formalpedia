-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_6_4
-- name    : RandomLPIPM.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:15.851128+00:00
-- url     : https://prove2.me/theorems/2ee63b2f-2905-4a88-8415-4b0929fbd0f1
-- title:
--   Lemma 6.4 — $\|x_\mu-\mathbf 1\|_\infty,\|s_\mu-\mathbf 1\|_\infty=O((1-\mu)\sqrt{\log n})$ w.h.p.
-- statement:
--   Let $c\in(0,1/2]$, $cn\le d\le(1-c)n$, and $A\in\mathbb R^{d\times n}$ with independent $\mathcal N(0,1)$ entries. Fix $\mu\in(0,1]$. For every $q>0$ there are $K>0$ and $N_0$, depending only on $c$ and $q$, such that for $n\ge N_0$, with probability at least $1-n^{-q}$,
--   $$\|x_\mu-\mathbf 1\|_\infty\le K(1-\mu)\sqrt{\log n},\qquad \|s_\mu-\mathbf 1\|_\infty\le K(1-\mu)\sqrt{\log n}.$$
--
--   These are the other half of the norm hypotheses (64): no single coordinate of the central path point moves much.
--
--   Differences from the source:
--   - reading: w.h.p., O((1 − μ)√log n) → ∀ q > 0 ∃ K > 0, N₀ (depending only on c, q) such that for n ≥ N₀ and every μ ∈ (0,1] both bounds hold with constant K except with probability ≤ n^(−q); reason: the paper's definition of w.h.p. (p.21) with the failure exponent arbitrary, as its proofs deliver (p.56, p.81)
--   - encoding: (x_μ, s_μ) the solution of the central path equations → x_μ the log-barrier minimizer, s_μ = μ/x_μ; reason: equivalent by p.22
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.4, p.45

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_sMu
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Lemma 6.4 (Central-Path Points ℓ∞ Upper Bounds).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.4, p.45.

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries, and fix
`μ ∈ (0, 1]`. Then w.h.p. `‖x_μ − 1‖_∞ ≤ O((1 − μ)√(log n))` and `‖s_μ − 1‖_∞ ≤ O((1 − μ)√(log n))`.

**Formalization Note.** "w.h.p." and `Ω(·)`/`O(·)` (p.21) are read as: for every exponent `q > 0` there are constants
depending only on `c` and `q` and a threshold `N₀` such that for `n ≥ N₀` the failure probability is
at most `n^{−q}`; the constant `K` of `O` is one constant for both bounds and all
`μ ∈ (0, 1]`. -/
theorem lemma_6_4 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
    GaussianMatrix.gaussianMatrix d n {A | ¬ (
        ColumnRandLP.supNorm (xMu (Matrix.of A) μ - 1) ≤ K * ((1 - μ) * Real.sqrt (Real.log n)) ∧
        ColumnRandLP.supNorm (sMu (Matrix.of A) μ - 1) ≤ K * ((1 - μ) * Real.sqrt (Real.log n)))} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
