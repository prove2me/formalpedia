-- Prove2me | Theorems.Thm_STOC2027BoolCSP_Approximation_lemma_7_2
-- name    : STOC2027BoolCSP.Approximation.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:00.490837+00:00
-- url     : https://prove2.me/theorems/6f68f5d5-0d89-4189-8543-7f8342690094
-- title:
--   Lemma 7.2 — rational score factor
-- statement:
--   Fix $k\ge5$, $m=k+1$ and $\delta=\pi/m$. Let $B$ be a rational $N\times N$ matrix with $B\succeq0$ and $B_{ii}=1$ (the shared block of a feasible Gram matrix), and $H=\delta B+(1-\delta)I_N$. For every rational $0<\mu\le1$, a rational matrix $\tilde A$ with
--   $$\|\tilde A-H^{1/2}\|_{op}\;\le\;\mu$$
--   can be computed in time polynomial in the bit length of $B$, $N$ and $\log(1/\mu)$. Here $H^{1/2}$ is the positive semidefinite square root and $\|\cdot\|_{op}$ the Euclidean operator norm. One fixed machine does this for all $B$ and $\mu$.
--
--   The factor turns independent scalar samples into the joint score vector $S=H^{1/2}Z$, whose law is exactly that of the rounding (28).
--
--   Differences from the source:
--
--   - encoding: an algorithm (deterministic, polynomial time) → a fixed CoinMachine (Mathlib FinTM2 with finite stack alphabets and bit input/output stacks) run on the empty random tape, halting within P(1 + input length + precision) steps with the coded output; reason: ordinary finite-alphabet Turing computation, the model the paper's Section 7 names; one step is a bounded number of bit operations
--   - reading: time polynomial in the bit length of B, N and log(1/μ) → steps ≤ P(1 + |code(B) ++ code(μ)| + p(μ)), with N written in unary inside code(B); reason: the accuracy's representation is part of the input (preamble of Section 1.1); N is bounded by the code length
--   - generalization: B the shared block of a feasible normalized conjunction instance, with N = n + 1 → every rational PSD matrix with unit diagonal in every dimension N ≥ 0; reason: every source block satisfies these hypotheses; the factor construction uses only PSD and unit diagonal for N > 0, and the unique empty matrix handles N = 0
--   - encoding: H^{1/2}, ‖·‖_op → CFC.sqrt for the Loewner order; norm of Matrix.toEuclideanCLM; reason: Mathlib's PSD square root and ℓ² operator norm
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 14 (PDF 17), Lemma 7.2 (with equation (34))

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_Machine
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation

/-- Lemma 7.2 (rational score factor), printed p. 14: for the rational shared block `B`
(`B ⪰ 0`, `B_ii = 1`) and every rational `0 < μ ≤ 1`, one fixed machine computes a rational
`Ã` with `‖Ã − H^{1/2}‖_op ≤ μ`, `H = δB + (1−δ)I_N`, `δ = π/(k+1)`, in time polynomial in the
bit length of `B`, `N` and `log(1/μ)`. -/
theorem lemma_7_2 (k : ℕ) (hk : 5 ≤ k) :
    ∃ (Mach : CoinMachine) (P : Polynomial ℕ), ∀ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℚ),
      (ratToReal B).PosSemidef → (∀ i, B i i = 1) → ∀ μ : ℚ, 0 < μ → μ ≤ 1 →
        ∃ A : Matrix (Fin N) (Fin N) ℚ,
          Mach.HaltsWithin (sqMatCode B ++ ratCode μ) []
            (P.eval (1 + (sqMatCode B ++ ratCode μ).length + precBits μ)) (sqMatCode A) ∧
          opNorm (ratToReal A - psdSqrt (scoreCov k (ratToReal B))) ≤ μ := by sorry

end STOC2027BoolCSP.Approximation
