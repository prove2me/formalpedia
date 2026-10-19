-- Prove2me | Theorems.Thm_QAlgorithms_Papers_IQAE21_iqae_clopperPearson_correct
-- name    : QAlgorithms.Papers.IQAE21.iqae_clopperPearson_correct
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:09:42.485633+00:00
-- url     : https://prove2.me/theorems/7083497f-128c-4d14-a063-3492ee1283c3
-- title:
--   IQAE with Clopper–Pearson intervals: round, iteration and query bounds and 0.95 confidence
-- statement:
--   Let $A$ be a unitary on $n+1$ qubits such that
--
--   $$A|0\rangle_n|0\rangle=\sqrt{1-a}\,|\psi_0\rangle_n|0\rangle+\sqrt{a}\,|\psi_1\rangle_n|1\rangle,$$
--
--   where $a\in[0,1]$ is unknown and $|\psi_0\rangle,|\psi_1\rangle$ are unit vectors (not necessarily orthogonal); the last qubit is the flag qubit. Let $\theta_a=\arcsin\sqrt a$, so $a=\sin^2\theta_a$, and let $Q=AS_0A^\dagger S_{\psi_0}$ with $S_0=I-2|0\rangle\langle0|_{n+1}$ and $S_{\psi_0}=I-2|\psi_0\rangle\langle\psi_0|\otimes|0\rangle\langle0|$.
--
--   Run Iterative Quantum Amplitude Estimation (Algorithm 1 with the subroutine FindNextK, $r=2$) with Clopper–Pearson confidence intervals at per-round level $\alpha/T$, where $T=\lceil\log_2(\pi/(8\varepsilon))\rceil$; each iteration measures the flag qubit of $Q^{k_i}A|0\rangle$ a number of times and updates a confidence interval $[\theta_l,\theta_u]$ for $\theta_a$. Fix $\alpha=1/20$, a target accuracy $2^{-200}\le\varepsilon<\pi/8$, and an integer number of shots $1\le N_{\mathrm{shots}}\le N_{\max}(\varepsilon,\alpha)$, where
--
--   $$N_{\max}(\varepsilon,\alpha)=69\log\Big(\frac{2}{\alpha}\log_2\frac{\pi}{4\varepsilon}\Big).$$
--
--   Then:
--
--   1. the algorithm performs at most $T$ rounds (a round is the set of iterations with the same power $k_i$), each round has at most $N_{\max}/N_{\mathrm{shots}}$ iterations, and in particular the algorithm has terminated after $T\lfloor N_{\max}/N_{\mathrm{shots}}\rfloor$ iterations;
--   2. on every run, $\theta_u-\theta_l\le2\varepsilon$ and $a_u-a_l\le2\varepsilon$, where $[a_l,a_u]=[\sin^2\theta_l,\sin^2\theta_u]$ is the returned interval;
--   3. $\Pr[\theta_a\notin[\theta_l,\theta_u]]\le\alpha$;
--   4. $\Pr[a\notin[a_l,a_u]]\le\alpha$;
--   5. $\Pr\big[|a-\tilde a|>\varepsilon\big]\le\alpha$ for the estimate $\tilde a=(a_l+a_u)/2$;
--   6. on every run the total number of applications of $Q$, $N_{\mathrm{oracle}}=\sum_i N_ik_i$, satisfies
--
--   $$N_{\mathrm{oracle}}<\frac{14}{\varepsilon}\log\Big(\frac{2}{\alpha}\log_2\frac{\pi}{4\varepsilon}\Big).$$
--
--   This is the Clopper–Pearson variant of the correctness theorem of IQAE: amplitude estimation without phase estimation, with a quadratic speedup over Monte Carlo up to a double-logarithmic factor and explicit small constants.
--
--   **Formalization Note** The algorithm is a Markov chain on its classical state; shot counts are binomial with the exact quantum probability of the flag outcome. The chain is run for $T\lfloor N_{\max}/N_{\mathrm{shots}}\rfloor+1$ steps (the last step only evaluates the loop condition) and every reachable state must be halted. Two corrections of the page: the Clopper–Pearson bounds are used in their standard orientation (the paper prints $a^{\min}$ and $a^{\max}$ swapped in (C5)–(C6) and Alg. 1), and $\varepsilon<\pi/8$ is assumed, since for $\pi/8\le\varepsilon<\pi/4$ the printed algorithm has $T=0$ while its loop still runs.
-- source:
--   Iterative Quantum Amplitude Estimation (Grinko, Gacon, Zoufal, Woerner), arXiv:1912.05559v3, Appendix C, Theorem 2, PDF p. 11. https://arxiv.org/abs/1912.05559v3 . PDF SHA-256: 6974b27a44a38e1223ebaabc86a8be723e7f04d5494d40d73859b12f759ba6a1.

import Definitions.Def_QAlgorithms_Defs_IQAE
set_option autoImplicit false

namespace QAlgorithms.Papers.IQAE21

open QAlgorithms

/-- IQAE Theorem 2 (Appendix C, p.11; Algorithm 1, p.3; Algorithm 2, p.4; eq. (11), p.4;
Clopper–Pearson bounds (C5)–(C7), p.12): let `A` be a unitary on `n + 1` qubits with
`A|0⟩ = √(1 − a)|ψ₀⟩|0⟩ + √a|ψ₁⟩|1⟩` (eq. (1)), `a ∈ [0, 1]`, `|ψ₀⟩, |ψ₁⟩` unit vectors, and
`θ_a = arcsin √a` (`a = sin² θ_a`, eq. (4)). Take `α = 1/20` (confidence `0.95`),
`2^{−200} ≤ ε < π/8`, and `N_shots ∈ {1, …, N_max(ε, α)}`,
`N_max(ε, α) = 69 log((2/α) log₂(π/(4ε)))`. Then IQAE with Clopper–Pearson intervals:
1. performs at most `T = ⌈log₂(π/(8ε))⌉` rounds (a round is the set of iterations with the same
   `k_i`), each of at most `N_max/N_shots` iterations; hence it has halted after
   `T · ⌊N_max/N_shots⌋ + 1` steps of the chain (the last step only checks the loop condition);
2. on every run, `θ_u − θ_l ≤ 2ε` and `a_u − a_l ≤ 2ε`, where `[a_l, a_u] = [sin² θ_l, sin² θ_u]`;
3. `P[θ_a ∉ [θ_l, θ_u]] ≤ α`; 4. `P[a ∉ [a_l, a_u]] ≤ α`;
5. `P[|a − (a_l + a_u)/2| > ε] ≤ α`;
6. on every run, `N_oracle < (14/ε) log((2/α) log₂(π/(4ε)))` (C3).

Corrections of the page (recorded in the chunk's STATUS.md): the Clopper–Pearson bounds of
(C5)–(C6) and Alg. 1 lines 24–25 are printed with `a^min` and `a^max` swapped; the standard
orientation is used (frozen `clopperPearsonLower`/`Upper`). The hypothesis `ε < π/8` is added:
for `π/8 ≤ ε < π/4` the printed algorithm has `T = 0` rounds while its loop still runs, and its
level `α/(2T)` is undefined. -/
theorem iqae_clopperPearson_correct (n : ℕ) (A : Matrix (Qubits (n + 1)) (Qubits (n + 1)) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Qubits (n + 1)) ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ψ0 ψ1 : EuclideanSpace ℂ (Qubits n)) (hψ0 : ‖ψ0‖ = 1) (hψ1 : ‖ψ1‖ = 1)
    (hAeq : act A (zeroKet (n + 1)) =
      (Real.sqrt (1 - a) : ℂ) • snocQubit ψ0 false + (Real.sqrt a : ℂ) • snocQubit ψ1 true)
    (ε : ℝ) (hε0 : (2 : ℝ) ^ (-200 : ℤ) ≤ ε) (hε1 : ε < Real.pi / 8)
    (Nshots : ℕ) (hN1 : 1 ≤ Nshots) (hN2 : (Nshots : ℝ) ≤ iqaeNmax ε (1 / 20)) :
    let F : ℕ := iqaeT ε * ⌊iqaeNmax ε (1 / 20) / Nshots⌋₊ + 1
    let μ : PMF IQAEState := iqaeRun A ψ0 ε (1 / 20) Nshots F
    (∀ s ∈ μ.support,
      s.halted = true ∧
      s.kHist.dedup.length ≤ iqaeT ε ∧
      (∀ k ∈ s.kHist, (s.kHist.count k : ℝ) ≤ iqaeNmax ε (1 / 20) / Nshots) ∧
      s.thetaU - s.thetaL ≤ 2 * ε ∧
      Real.sin s.thetaU ^ 2 - Real.sin s.thetaL ^ 2 ≤ 2 * ε ∧
      (s.oracle : ℝ) < 14 / ε * Real.log (2 / (1 / 20) * Real.logb 2 (Real.pi / (4 * ε)))) ∧
    μ.toOuterMeasure {s | Real.arcsin (Real.sqrt a) ∉ Set.Icc s.thetaL s.thetaU} ≤
      ENNReal.ofReal (1 / 20) ∧
    μ.toOuterMeasure {s | a ∉ Set.Icc (Real.sin s.thetaL ^ 2) (Real.sin s.thetaU ^ 2)} ≤
      ENNReal.ofReal (1 / 20) ∧
    μ.toOuterMeasure {s | ε < |a - (Real.sin s.thetaL ^ 2 + Real.sin s.thetaU ^ 2) / 2|} ≤
      ENNReal.ofReal (1 / 20) := by
  sorry

end QAlgorithms.Papers.IQAE21
