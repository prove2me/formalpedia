-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_6_8
-- name    : TruncLowDeg.Recovery.lemma_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:25:25.580257+00:00
-- url     : https://prove2.me/theorems/5dbb53ef-69f3-4f35-9968-f6fa59f2e6d8
-- title:
--   Lemma 6.8 — an implementation of Algorithm 1 in $n\cdot d^{O(k)}$ steps that makes correct choices on the good event
-- statement:
--   There is an implementation of Algorithm 1 that runs in time $n\cdot d^{O(k)}$ such that under the event that the preconditioning works and (15) holds, it correctly computes all the choices required by the algorithm.
--
--   Formally: for every constant $C_4>0$ of Lemma 5.4 and every $\rho$-constant $c_\rho\ge1$ there is $N$ such that, for algorithm constants whose two constants of (14) are at least $N$, there are one admissible program $P$ of the deterministic real RAM with square root, a whitening rule $W$ of the preliminary batch (a whitening of $\hat\Sigma_{pre}$ whenever $\hat\Sigma_{pre}\succ0$, measurable in the samples), and $C>0$ such that for $d,k\ge1$, $\alpha_0\in(0,1]$, $\varepsilon,\delta\in(0,1)$ and every table of $n$ points: $P$ halts within $C\,n\,d^{Ck}$ steps, and whenever the good event holds for an instance $(\mu_0,\Sigma_0,S_0)$ of Theorem 6.1 and the rule $W$, the output of $P$ is an output Algorithm 1 can return with that whitening. This is the computational half of Theorem 6.1: (14) is solved through the regularized least-squares problem (17) and $\hat s_j$ through a linear system.
--
--   Differences from the source:
--
--   - reading: "runs in time"; "an implementation" → the number of executed instructions of an `Admissible` program of the deterministic unit-cost real RAM with square root (`Machine`: SmaleNinth core plus √, rational literals; no floor, exp/log, eigenvalue, SVD or matrix-square-root instruction, no randomness); reason: the paper names no machine; this is the weakest model in which the runtime analysis of pp. 34–35 goes through
--   - reading: an implementation of Algorithm 1 with Σ̂_pre^{−1/2} in lines 4 and 14 → the program's output is an output of Algorithm 1 for a whitening W of Σ̂_pre that the program chooses (∃ W, measurable in the samples); reason: the paper implements "a slight variant of Algorithm 1" (p. 27, p. 33); the PSD square root of a d × d matrix is not computable exactly by the machine (eigenvalues are not radical expressions for d ≥ 5), while a Cholesky whitening is; Proposition 6.7 holds for every whitening, so the chain to Theorem 6.1 is unchanged
--   - reading: a preliminary batch "of the size required by Lemma 5.4 with failure probability δ/2" (Õ(d³/α₀¹⁰ · log²(2/δ))) → `nPre = ⌈c_pre · d⁴/(α₀¹¹ δ)⌉` with the batch constant c_pre sufficiently large; reason: it dominates Lemma 5.4's requirement for large c_pre (polylog(d/α₀) ≤ O(d/α₀), log²(2/δ) = O(1/δ), as the paper notes on p. 28), is absorbed in the sample bound, and is computable with field operations and comparisons only (Lemma 6.8)
--   - generalization: the implicit constants → ∀ C₄ > 0, ∀ c_ρ ≥ 1, ∃ N, ∀ c with c_q, c_r ≥ N (c_pre, c_η arbitrary), ∃ P, W, C; reason: "choosing the implicit constants in (14) sufficiently large" (p. 34) is what makes every minimizer of (17) a solution of (14); every C₄ > 0, c_ρ ≥ 1, c_pre and c_η are covered, including the paper's, so it specializes
--   - encoding: runs in time n·d^{O(k)} → for every table of n points, some t ≤ C·n·d^{C·k} with the configuration halted at step t; reason: worst case on every input, as the proof of Theorem 6.1 requires ("always runs in time")
--   - encoding: "under the event … it correctly computes all the choices" → for every instance of Theorem 6.1 on whose good event the table lies, the decoded output at any halting time satisfies `Alg1Output`; reason: computing admissible choices in lines 9 and 11 means the returned value is an output of Algorithm 1
--   - encoding: the input (d, k, n, α₀, ε, δ, samples) and the output (µ̂₀, Σ̂₀) or Fail → `initConfig` (pointers d, k, n; memory α₀, ε, δ, samples row by row) and `output` (reject = Fail; accept = the output block); reason: input/output layout
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 33, Lemma 6.8; proof pp. 33–35

import Definitions.Def_TruncLowDeg_Recovery_Algorithm
import Definitions.Def_TruncLowDeg_Recovery_Machine

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 6.8 (p. 33): efficient implementation. For every constant `C₄` of Lemma 5.4 and every
`ρ`-constant `cρ ≥ 1` there is a threshold `N` such that, for Algorithm 1's constants with the
two constants of (14) at least `N`, there are one admissible program `P` of the real RAM with
square root, a whitening rule `W` of the preliminary batch (a whitening of `Σ̂_pre` whenever
`Σ̂_pre ≻ 0`, measurable as a function of the samples) and a constant `C` such that, for
`d, k ≥ 1`, `α₀ ∈ (0, 1]`, `ε, δ ∈ (0, 1)` and every table of `n` points: `P` halts within
`C n d^{Ck}` steps; and if, for an instance `(µ₀, Σ₀, S₀)` of Theorem 6.1, the preconditioning
works and (15) holds (the good event of Proposition 6.7 for the rule `W`), the output of `P` is
an output Algorithm 1 can return with the whitening `W` (it correctly computes all the choices).
-/
theorem lemma_6_8 :
    ∀ C₄ : ℝ, 0 < C₄ → ∀ cρ : ℕ, 1 ≤ cρ → ∃ N : ℕ,
      ∀ c : Consts, c.rho = cρ → N ≤ c.q → N ≤ c.r →
      ∃ (P : Program) (Wb : ∀ d : ℕ, List (Vec d) → Mat d) (C : ℝ),
        Admissible P ∧ 0 < C ∧
        (∀ (d : ℕ) (L : List (Vec d)), (empCov L).PosDef → IsWhitening (empCov L) (Wb d L)) ∧
        ∀ (d k n : ℕ) (α₀ ε δ : ℝ), 1 ≤ d → 1 ≤ k → 0 < α₀ → α₀ ≤ 1 → 0 < ε → ε < 1 →
          0 < δ → δ < 1 →
          (∀ i j : Fin d,
            Measurable (fun X : Fin n → Vec d => Wb d (batch c α₀ δ (List.ofFn X)) i j)) ∧
          ∀ X : Fin n → Vec d,
            (∃ t : ℕ, (t : ℝ) ≤ C * n * (d : ℝ) ^ (C * k) ∧
              Halted P (run P (initConfig d k n α₀ ε δ X) t)) ∧
            ∀ (μ₀ : Vec d) (Sig₀ : Mat d) (S₀ : Set (Vec d)), Sig₀.PosDef →
              BVD S₀ ≤ (k : ℕ∞) → ENNReal.ofReal α₀ ≤ gaussian μ₀ Sig₀ S₀ →
              Good c C₄ d k α₀ ε δ μ₀ Sig₀ S₀ (List.ofFn X)
                (Wb d (batch c α₀ δ (List.ofFn X))) →
              ∀ t : ℕ, Halted P (run P (initConfig d k n α₀ ε δ X) t) →
                Alg1Output c d k α₀ ε δ (List.ofFn X) (Wb d (batch c α₀ δ (List.ofFn X)))
                  (output P d (run P (initConfig d k n α₀ ε δ X) t)) := by sorry

end TruncLowDeg.Recovery
