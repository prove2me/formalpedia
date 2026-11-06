-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_2_2
-- name    : RandomLPIPM.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:17.27142+00:00
-- url     : https://prove2.me/theorems/83160923-9335-4c91-92c7-a871902a347d
-- title:
--   Theorem 2.2 — central-path conditioned projection bound: $\|P(AX_\mu)\mathbf 1\|_\infty=O((\log n)^{4.5})$ w.h.p.
-- statement:
--   Let $c\in(0,1/2]$ and $cn\le d\le(1-c)n$. Let $A\in\mathbb R^{d\times n}$ have independent $\mathcal N(0,1)$ entries. For a fixed $\mu\in(0,1]$ let $x_\mu$ be the $\mu$-central path point of LP(A) and $X_\mu=\operatorname{Diag}(x_\mu)$. Then for every $q>0$ there are $K>0$ and $N_0$, depending only on $c$ and $q$, such that for $n\ge N_0$ and every $\mu\in(0,1]$,
--   $$\Pr\big[\|P(AX_\mu)\mathbf 1_n\|_\infty>K(\log n)^{4.5}\big]\le n^{-q}.$$
--
--   By Eq. (2), $P(AX_\mu)\mathbf 1=d\log s_\mu/d\log\mu$, so this bounds the multiplicative speed of the central path at a fixed $\mu$ by a polylogarithm, against the worst-case $\sqrt n$. It is the paper's key result.
--
--   Differences from the source:
--   - reading: with high probability over A, O((log n)^4.5) → ∀ q > 0 ∃ K > 0, N₀ (depending only on c, q) such that for n ≥ N₀ and every μ ∈ (0,1] the failure probability is ≤ n^(−q); reason: p.21; p.56: 'Since C_q depends only on q and c, and the bound holds for every μ ∈ (0,1]'
--   - encoding: P(M) := Mᵀ(MMᵀ)⁻¹M → orthogonal projector onto the row space of M; reason: equal for full-row-rank M, which AX_μ is almost surely
--   - encoding: probability of the event → outer Gaussian measure of the failure set bounded by the failure probability; reason: no measurability assumption is needed; for a measurable event it is 1 − P(event)
--   - encoding: x_μ the solution of the central path equations → x_μ the log-barrier minimizer; reason: equivalent by p.22
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 2.2, p.9; proof in §6.3, p.56

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_projRow
import Definitions.Def_ColumnRandLP_Norms

open Matrix MeasureTheory

namespace RandomLPIPM

/-- **Theorem 2.2 (Central-Path Conditioned Projection Bound).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 2.2, p.9 (proved in
§6.3, p.56).

Let `c ∈ (0, 1/2]`, `cn ≤ d ≤ (1 − c)n`, `A ∈ ℝ^{d×n}` with independent `N(0,1)` entries, `μ ∈ (0, 1]`
fixed and `x_μ` the `μ`-central path point of LP(A). Then w.h.p. over `A`,
`‖P(AX_μ)·1‖_∞ ≤ O((log n)^{4.5})`.

**Formalization Note.** "w.h.p." and `Ω(·)`/`O(·)` (p.21) are read as: for every exponent `q > 0` there are constants
depending only on `c` and `q` and a threshold `N₀` such that for `n ≥ N₀` the failure probability is
at most `n^{−q}`; `K` and `N₀` are uniform in `μ ∈ (0, 1]` (p.56: "Since `C_q` depends
only on `q` and `c`, and the bound holds for every `μ ∈ (0, 1]`"). `X_μ = Diag(x_μ)`. -/
theorem theorem_2_2 :
    ∀ c : ℝ, 0 < c → c ≤ 1 / 2 → ∀ q : ℝ, 0 < q →
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n d : ℕ, N₀ ≤ n → c * n ≤ d → (d : ℝ) ≤ (1 - c) * n →
    ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
    GaussianMatrix.gaussianMatrix d n {A | K * Real.log n ^ (9 / 2 : ℝ) <
        ColumnRandLP.supNorm (projRow (Matrix.of A * diagonal (xMu (Matrix.of A) μ)) 1)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-q)) := by sorry

end RandomLPIPM
