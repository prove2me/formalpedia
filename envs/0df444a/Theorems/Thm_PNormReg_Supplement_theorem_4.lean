-- Prove2me | Theorems.Thm_PNormReg_Supplement_theorem_4
-- name    : PNormReg.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:55:11.495659+00:00
-- url     : https://prove2.me/theorems/675705e0-b5a4-4181-b48e-20d80413276c
-- title:
--   Theorem 4, p.9 — from $\eta$-improvement oracles to a $(1+\epsilon)$-approximate solution, in time $\widetilde O(\mathrm{nnz}(A)+d^\omega)$ plus the oracle calls
-- statement:
--   Let $A\in\mathbb R^{n\times d}$ have full column rank, $b\in\mathbb R^n$, $p\in[1,\infty]$, $\epsilon,\delta\in(0,1)$ and $T=1+\lceil\log_2(2n)\rceil$. There is an algorithm with access to an $\eta$-improvement oracle (Definition 1) which outputs a $(1+\epsilon)$-approximate solution of $\min_x\|Ax-b\|_p$ with probability at least $1-\delta$, in time
--
--   $$\widetilde O\big(\mathrm{nnz}(A)+d^\omega+T^{\mathrm{Imp}}_{4/\epsilon}+T^{\mathrm{Imp}}_4\big),$$
--
--   where $T^{\mathrm{Imp}}_\eta$ is the cost of querying an $\eta$-improvement oracle with failure probability at most $\delta/(2T)$. Precisely: for every $\tau>0$ there are one oracle program and constants $C>0$, $K\in\mathbb N$ such that, for every valid randomized improvement oracle and with $L=\log(2+n+1/\epsilon+1/\delta)$,
--
--   1. on every program tape and every choice of oracle tapes the run halts after at most $C(\mathrm{nnz}(A)+n^\tau d^\omega)L^K$ non-oracle steps and at most $C L^K$ oracle calls, each with $\eta\in\{4,4/\epsilon\}$ and failure parameter $\delta/(2T)$;
--   2. with probability at least $1-\delta$ over the program's and the oracle's coins, the output $\hat x$ satisfies $\|A\hat x-b\|_p\le(1+\epsilon)\|Ax-b\|_p$ for all $x$.
--
--   This is the reduction of $\ell_p$-regression, for every $p\in[1,\infty]$, to a polylogarithmic number of bounded-domain additive subproblems.
--
--   **Formalization Note** The oracle machine and the oracle specification are `PNormReg.Supplement.OracleMachine` and `PNormReg.Supplement.Oracles`; oracle calls cost no work. Queries may depend on earlier answers. $\lceil\log_2(2n)\rceil$ is `Nat.clog 2 (2n)`. $p$ is passed as $1/p$.
--
--   Differences from the source:
--   - reading: "there is an algorithm" (no machine named) → one finite admissible program of the base machine extended by an oracle-call instruction (PNormReg.Supplement.OracleMachine); reason: the paper fixes no machine; same reading as the published goal Theorem 2
--   - reading: Õ(·) (footnote 2: n^{o(1)} from fast matrix multiplication and polylog factors in n, d, 1/ϵ, 1/δ) → for every τ > 0 one program with constants C, K: n^τ on the fast-matrix-multiplication term only, (log(2 + n + 1/ϵ + 1/δ))^K on the whole bound; reason: footnote 2 pins the hidden factors; same reading as Theorem 2
--   - reading: time Õ(… + T^Imp_{4/ϵ} + T^Imp_4), T^Imp_η the cost of a query with failure probability at most δ/(2T) → oracle calls cost 0 work; separately, at most C·L^K calls, each with η ∈ {4, 4/ϵ} and failure parameter exactly δ/(2T); reason: the formal content of an oracle-relative running time; Algorithm 1 sets these parameters (lines 1, 4)
--   - reading: an η-improvement oracle (Definition 1) "with probability at least 1 − δ′" → every valid randomized oracle: private fair-coin tape per call, adaptive queries, each answer correct with probability ≥ 1 − δ′, jointly measurable; reason: measurability is the standing convention that makes the probability of an adaptive run defined
--   - encoding: p ∈ [1, ∞] → pInv = 1/p ∈ [0, 1], pInv = 0 for p = ∞; reason: the paper's 1/∞ = 0
--   - encoding: ⌈log₂(2n)⌉ → Nat.clog 2 (2n); reason: equal for every n ≥ 1
--   - encoding: input of problem (1) → sparse layout: nonzero entries of A with positions, then b; header 1/p, ϵ, δ; reason: a dense matrix cannot be read in nnz(A) time; the paper names no format
--   - encoding: with probability at least 1 − δ → a measurable set of joint (program and oracle) tapes of probability ≥ 1 − δ on which the halted output satisfies the bound against every x; reason: the minimum exists, so "for every x" is the same condition; same as Theorem 2
--   - encoding: A ∈ ℝ^{n×d} (d ≥ 1 implicit) → 1 ≤ d; reason: excludes only the empty problem, where a zero time bound would forbid halting
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Theorem 4, p.9 (PDF p.10); Definition 1, p.8; §2.1 preamble, p.8; problem (1) and footnotes 1–2, p.1

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_PNormReg_Supplement_Oracles

open Matrix

namespace PNormReg

namespace Supplement

/-- **Theorem 4** (from `η`-improvement oracles to a `(1+ϵ)`-approximate solution of (1)).

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*, STOC 2027
submission (manuscript sha256 e335b2fa…), Theorem 4, p.9 (PDF p.10); Definition 1, p.8; §2.1's "we fix any p ∈ [1, ∞]", p.8;
problem (1) and footnotes 1–2, p.1.

"Let ϵ, δ ∈ (0, 1) and T := 1 + ⌈log2(2n)⌉. There is an algorithm that outputs a (1 + ϵ)-approximate
solution to (1) with probability at least 1 − δ in time Õ(nnz(A) + d^ω + T^Imp_{4/ϵ} + T^Imp_4), where T^Imp_η
is the cost of querying an η-improvement oracle (Definition 1) with failure probability at most δ/(2T)."

For every `τ > 0` there are one admissible oracle program `P` and `C > 0`, `K ∈ ℕ` such that for all
`n`, `d ≥ 1`, full column rank `A`, `b`, `p ∈ [1, ∞]` (given as `pInv = 1/p ∈ [0, 1]`), `ϵ, δ ∈ (0, 1)`
and every valid randomized `η`-improvement oracle `O` for `f_p`, with `T = 1 + ⌈log₂(2n)⌉` and
`L = log(2 + n + 1/ϵ + 1/δ)`:
1. on every program tape and every family of oracle tapes the run halts, with non-oracle work at most
   `C·(nnz(A) + n^τ·d^ω)·L^K`, at most `C·L^K` oracle calls, and every call made with parameter
   `η ∈ {4, 4/ϵ}` and failure parameter `δ/(2T)`;
2. on a measurable set of joint tapes of probability at least `1 − δ` the output `x̂` satisfies
   `∥Ax̂ − b∥_p ≤ (1 + ϵ)∥Ax − b∥_p` for all `x`.

**Formalization Note.**
* "Time `Õ(… + T^Imp_{4/ϵ} + T^Imp_4)`" is read as: oracle calls cost `0` work and are bounded
  separately, by their number (polylogarithmic, the `Õ`) and their parameters (`η ∈ {4, 4/ϵ}`, failure
  exactly `δ/(2T)`, Algorithm 1 line 1). The oracle machine is `PNormReg.Supplement.OracleMachine`.
* The guarantee holds for every valid oracle: each answer meets (4) with probability at least
  `1 − δ'` on that call's own fair-coin tape, queries may depend on earlier answers, and the oracle is
  jointly measurable (the standing convention behind "with probability at least").
* `⌈log₂(2n)⌉` is `Nat.clog 2 (2n)`, equal to it for every `n ≥ 1` (and `n ≥ d ≥ 1` here).
* `Õ` (footnote 2): `n^τ` on the fast-matrix-multiplication term `d^ω` only; the log power on the whole
  bound. No `p` factor: §2.1 holds for every `p ∈ [1, ∞]` with `Õ`, not `Õ_p`.
* Input: `sparseInput [pInv, ϵ, δ] A b`; oracle interface `improveIface d`.
* `d ≥ 1`: the problem is empty at `d = 0`. -/
theorem theorem_4 :
    ∀ τ : ℝ, 0 < τ →
      ∃ (P : OProgram) (_ : OAdmissible P) (C : ℝ) (K : ℕ), 0 < C ∧
        ∀ (n d : ℕ), 1 ≤ d → ∀ (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
          Function.Injective A.mulVec →
          ∀ pInv ε δ : ℝ, 0 ≤ pInv → pInv ≤ 1 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          ∀ O : ImproveQuery d → (ℕ → Bool) → (ℕ → ℝ),
            ValidOracle (improveSpec A b pInv) (fun q => q.2.1) O →
            (∀ (ω : ℕ → Bool) (Ω : ℕ → ℕ → Bool), ∃ t : ℕ,
              (orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) ω Ω t).base.halted = true ∧
              ((orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) ω Ω t).base.work : ℝ) ≤
                C * ((nnz A : ℝ) + (n : ℝ) ^ τ *
                    (d : ℝ) ^ OAI.MatrixMultiplication.Arithmetic.omega ℝ) *
                  Real.log (2 + n + 1 / ε + 1 / δ) ^ K ∧
              ((orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) ω Ω t).calls : ℝ) ≤
                C * Real.log (2 + n + 1 / ε + 1 / δ) ^ K ∧
              ∀ q ∈ (orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) ω Ω t).log,
                (q.1 = 4 ∨ q.1 = 4 / ε) ∧
                  q.2.1 = δ / (2 * ((1 + Nat.clog 2 (2 * n) : ℕ) : ℝ))) ∧
            ∃ E : Set ((ℕ → Bool) × (ℕ → ℕ → Bool)), MeasurableSet E ∧
              1 - δ ≤ (jointTape E).toReal ∧
              ∀ z ∈ E, ∀ t : ℕ,
                (orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) z.1 z.2 t).base.halted =
                    true →
                ∀ x : Fin d → ℝ,
                  fP A b pInv (outputVec d
                      (orun P (improveIface d) O (sparseInput [pInv, ε, δ] A b) z.1 z.2 t).base) ≤
                    (1 + ε) * fP A b pInv x := by sorry

end Supplement

end PNormReg
