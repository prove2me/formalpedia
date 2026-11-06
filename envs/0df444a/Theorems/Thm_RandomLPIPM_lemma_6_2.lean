-- Prove2me | Theorems.Thm_RandomLPIPM_lemma_6_2
-- name    : RandomLPIPM.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:12.882199+00:00
-- url     : https://prove2.me/theorems/33269a56-0b8e-49aa-bd37-273506fc8525
-- title:
--   Lemma 6.2 — central path points are $\ell_2$-far from $\mathbf 1$ and $\mu\mathbf 1$: $\Omega((1-\mu)\sqrt n)$ w.h.p.
-- statement:
--   Let $c\in(0,1/2]$, $cn\le d\le(1-c)n$, and $A\in\mathbb R^{d\times n}$ with independent $\mathcal N(0,1)$ entries. For $\mu\in(0,1]$ let $x_\mu=x_\mu(A)$, $s_\mu=s_\mu(A)$. For every $q>0$ there are $c_1>0$ and $N_0$, depending only on $c$ and $q$, such that for $n\ge N_0$ and every $\mu\in(0,1]$, with probability at least $1-n^{-q}$,
--   $$\|x_\mu-\mathbf 1\|_2,\ \|s_\mu-\mathbf 1\|_2,\ \|x_\mu-\mu\mathbf 1\|_2,\ \|s_\mu-\mu\mathbf 1\|_2\ \ge\ c_1(1-\mu)\sqrt n .$$
--
--   These lower bounds say the central path point is "balanced": its deviation from the all-ones vector is spread over $\Omega(n)$ coordinates. They are half of the norm hypotheses (64) of Lemma 6.9.
--
--   Differences from the source:
--   - reading: w.h.p., Ω((1 − μ)√n) → ∀ q > 0 ∃ c₁ > 0, N₀ (depending only on c, q) such that for n ≥ N₀ and every μ ∈ (0,1] all four bounds hold with constant c₁ except with probability ≤ n^(−q); reason: the paper's definition of w.h.p. (p.21) with the failure exponent arbitrary, as its proofs deliver (p.56, p.81)
--   - encoding: (x_μ, s_μ) the solution of x·s = μ1, x − 1 ∈ ker A, s − 1 ∈ im Aᵀ → x_μ the log-barrier minimizer, s_μ = μ/x_μ; reason: equivalent by p.22
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.2, p.43

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_sMu
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Lemma 6.2 (Central-Path Points ℓ2 Lower Bounds).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 6.2, p.43.

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries, and
`μ ∈ (0, 1]`. Then w.h.p. `‖x_μ − 1‖₂, ‖s_μ − 1‖₂, ‖x_μ − μ1‖₂, ‖s_μ − μ1‖₂ ≥ Ω((1 − μ)√n)`.

**Formalization Note.** "w.h.p." and `Ω(·)`/`O(·)` (p.21) are read as: for every exponent `q > 0` there are constants
depending only on `c` and `q` and a threshold `N₀` such that for `n ≥ N₀` the failure probability is
at most `n^{−q}`; the constant `c₁` of `Ω` is one constant for all four bounds and all
`μ ∈ (0, 1]`. -/
theorem lemma_6_2 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
    GaussianMatrix.gaussianMatrix d n {A | ¬ (
        c₁ * ((1 - μ) * Real.sqrt n) ≤ ColumnRandLP.l2Norm (xMu (Matrix.of A) μ - 1) ∧
        c₁ * ((1 - μ) * Real.sqrt n) ≤ ColumnRandLP.l2Norm (sMu (Matrix.of A) μ - 1) ∧
        c₁ * ((1 - μ) * Real.sqrt n) ≤ ColumnRandLP.l2Norm (xMu (Matrix.of A) μ - μ • (1 : Fin n → ℝ)) ∧
        c₁ * ((1 - μ) * Real.sqrt n) ≤ ColumnRandLP.l2Norm (sMu (Matrix.of A) μ - μ • (1 : Fin n → ℝ)))} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
