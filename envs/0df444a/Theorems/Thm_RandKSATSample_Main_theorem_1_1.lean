-- Prove2me | Theorems.Thm_RandKSATSample_Main_theorem_1_1
-- name    : RandKSATSample.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:00:25.208019+00:00
-- url     : https://prove2.me/theorems/4b8f70f1-608c-4022-85f4-6a6b7f8743c6
-- title:
--   Theorem 1.1 — k ≥ 2^20, α ≤ 2^k/k^16: w.h.p. over Φ(k, n, ⌊αn⌋) one fair-coin program samples µ_Φ within TV ε ≥ n^{−B} in expected time C_B(k+α+1)^d(1+log n)^c n^{2+η}, 0 < η ≤ 2^{16−k}
-- statement:
--   There are one randomized program $P$ on the log-cost RAM, using only fair coins, and universal constants $d,c\in\mathbb N$ such that: for every $B>0$ there is $C_B>0$ such that for every integer $k\ge2^{20}$ and every real density $0<\alpha\le2^k/k^{16}$ there is $\eta$ with $0<\eta\le2^{16-k}$ such that, with probability tending to $1$ as $n\to\infty$ over $\Phi\sim\Phi(k,n,m)$ with $m=\lfloor\alpha n\rfloor$, the following holds simultaneously for every real $\varepsilon$ with $n^{-B}\le\varepsilon\le1/2$: on input $(\Phi,\varepsilon)$, $P$ terminates almost surely, outputs a satisfying assignment $X$ of $\Phi$ on every run, and
--   $$\|\mathrm{Law}(X)-\mu_\Phi\|_{TV}\le\varepsilon,\qquad\mathbb E[T]\le C_B\,(k+\alpha+1)^d\,(1+\log n)^c\,n^{2+\eta},$$
--   where $T$ is the running time. This is the paper's main result: almost-uniform sampling of random $k$-SAT solutions up to density $2^k/k^{16}$, with exponent of $n$ equal to $2+\eta$ and a polynomial in $(k,\alpha+1)$ of universal degree.
--
--   **Formalization Note.** $\Phi$ is in memory as `encFormula Φ`; $\varepsilon$ is read through `epsOracle ε` (its binary digits, and fresh fair bits); the program is `GenCountSampleLLL.Admissible` (no exact-Bernoulli instruction); halting, outputs and expected cost are `HaltsAS`, `OutputsSatisfy`, `expCost` (log-cost, in $[0,\infty]$, nonhalting runs charged); "with high probability" is $\forall\delta>0\ \exists N\ \forall n\ge N$, probability $\ge1-\delta$.
--
--   Differences from the source:
--   - reading: E[T] ≤ Õ_B(poly(k, α + 1) n^{2+η}), polynomial of universal degree, Õ_B hiding factors polylogarithmic in n and a constant depending on B → expCost ≤ C_B (k + α + 1)^d (1 + log n)^c n^{2+η}, with d, c universal (chosen before B) and C_B depending on B only; reason: the stronger of the readings: the polylog exponent c does not depend on B; (k + α + 1)^d bounds every polynomial in (k, α + 1) of degree d up to a constant
--   - encoding: time T = number of bit operations of 'our randomized algorithm' → ∃ program on the published log-cost oracle RAM PDSEquiv.Machine, fair bits only (Admissible), expCost in ℝ≥0∞; reason: log-cost charging is within polylogarithmic factors of bit operations, which Õ_B absorbs; the program reads only (Φ, ε) and is fixed before B, k, α, n, ε
--   - encoding: ε given under the binary input convention of §6.2 → every real ε, read through the oracle query [0, j] ↦ j-th binary digit ⌊2^j ε⌋ mod 2; reason: the convention of §6.2 (terminating expansion for dyadic inputs)
--   - encoding: with high probability over Φ ∼ Φ(k, n, m), for all n above a threshold depending on k, α, B → ∀ δ > 0, ∃ N, ∀ n ≥ N, probF n ⌊αn⌋ k (good event) ≥ 1 − δ; reason: probability tending to 1 (Lemma 3.13, proof p. 63); N may depend on k, α, B, δ
--   - encoding: ∥Law(X) − µ_Φ∥_TV ≤ ε; outputs a satisfying assignment → tvDist (outLaw P ε Φ) (muPhi Φ) ≤ ε over all assignments, and OutputsSatisfy: every halted output encodes a satisfying assignment; reason: (2.1) is ½ ℓ¹; the output law is the probability of halting with each encoded assignment
-- source:
--   He, Li, Yang, Fast Almost-Uniform Sampling of Random k-SAT Solutions, arXiv:2610.10474 (version not printed; file sha256 563a4d84…), p. 5, Theorem 1.1 (proof p. 63)

import Mathlib
import Definitions.Def_RandKSATSample_Main_Formula
import Definitions.Def_RandKSATSample_Main_Sampler
import Definitions.Def_PDSEquiv_Machine
import Definitions.Def_GenCountSampleLLL_csOracle
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

open scoped BigOperators ENNReal

namespace RandKSATSample.Main

/-- Theorem 1.1: one fair-coin program on the log-cost RAM and universal degrees `d, c` such that
for every `B > 0` there is `C_B > 0`, for every integer `k ≥ 2^20` and real `0 < α ≤ 2^k/k^16`
there is `η ∈ (0, 2^{16−k}]`, and with probability tending to `1` over `Φ ∼ Φ(k, n, ⌊αn⌋)`, for
every real `ε ∈ [n^{−B}, 1/2]` the program on `(Φ, ε)` halts almost surely, outputs a satisfying
assignment on every branch, has output law within total variation `ε` of `µ_Φ`, and expected
log-cost at most `C_B (k + α + 1)^d (1 + log n)^c n^{2+η}`. -/
theorem theorem_1_1 :
    ∃ (P : PDSEquiv.Program) (d c : ℕ), GenCountSampleLLL.Admissible P ∧
      ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
        ∀ k : ℕ, 2 ^ 20 ≤ k → ∀ α : ℝ, 0 < α → α ≤ (2 : ℝ) ^ k / (k : ℝ) ^ 16 →
          ∃ η : ℝ, 0 < η ∧ η ≤ (2 : ℝ) ^ ((16 : ℤ) - k) ∧
            ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              1 - δ ≤ probF n ⌊α * n⌋₊ k (fun Φ =>
                ∀ ε : ℝ, (n : ℝ) ^ (-B) ≤ ε → ε ≤ 1 / 2 →
                  GenCountSampleLLL.HaltsAS P (epsOracle ε) (encFormula Φ) ∧
                  PDSEquiv.OutputsSatisfy P (epsOracle ε) (encFormula Φ)
                    (fun o => ∃ σ : Assignment n, o = encAssign σ ∧ Sat Φ σ) ∧
                  IsingLTL.BeliefProp.tvDist (outLaw P ε Φ) (muPhi Φ) ≤ ε ∧
                  GenCountSampleLLL.expCost P (epsOracle ε) (encFormula Φ) ≤
                    ENNReal.ofReal (C * ((k : ℝ) + α + 1) ^ d * (1 + Real.log n) ^ c *
                      (n : ℝ) ^ (2 + η))) := by sorry

end RandKSATSample.Main
