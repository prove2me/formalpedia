-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_simulated_annealing_samples
-- name    : SKAnnealing.Sampling.simulated_annealing_samples
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:48.751815+00:00
-- url     : https://prove2.me/theorems/5a9979f6-fb69-4d0e-af72-22865bc13c6e
-- title:
--   Theorem 1.1, p. 1 — simulated annealing with gap $c/N$ and $O(N\log N)$ steps per temperature samples the SK measure to $d_{\mathrm{TV}}\le N^{-a}$ w.p. $1-N^{-a}$, all $\beta<1$
-- statement:
--   Let $W\sim\mathrm{GOE}(N)$ and let $\mu_{\beta W}(\sigma)\propto\exp\big(\frac\beta2\langle\sigma,W\sigma\rangle\big)$ be the Sherrington–Kirkpatrick Gibbs measure on $\{\pm1\}^N$. **Simulated annealing** with inverse temperature gap $c/N$ and $m$ steps per temperature starts from the uniform distribution on $\{\pm1\}^N$ and, for $j=1,\dots,L=\lceil\beta N/c\rceil$, runs $m$ steps of Glauber dynamics for $\mu_{\beta_jW}$, $\beta_j=\min(jc/N,\beta)$. Let $\widehat\mu=\widehat\mu_{W,\beta,c,m}$ be the exact law of its output.
--
--   **Theorem 1.1.** There is a universal constant $c_0>0$ such that for every $0\le\beta<1$, every $a>0$ and every $c\in(0,c_0]$ there are constants $C$ and $N_0$ with the following property: for every $N\ge N_0$ and every number of steps per temperature $m\ge C\,N\log N$,
--   $$\Pr_{W\sim\mathrm{GOE}(N)}\Big[d_{\mathrm{TV}}\big(\widehat\mu,\mu_{\beta W}\big)>N^{-a}\Big]\le N^{-a}.$$
--
--   The randomness is over the disorder $W$ only; $\widehat\mu$ is the exact output distribution of the algorithm. This is the first algorithm sampling the SK model for all $\beta<1$ up to an arbitrary inverse polynomial accuracy; earlier results reached total variation $o(1)$.
--
--   Differences from the source:
--   - reading: run for O_{a,β}(N log N) steps … per iteration, with inverse temperature gap c/N → ∃ universal c₀ > 0, ∀ c ∈ (0, c₀], ∃ C, N₀, ∀ N ≥ N₀, ∀ m ≥ C·N·log N; reason: the literal "some c and some m = O(N log N)" is weaker; Lemma 2.3's bound decreases in m and holds for every gap below c/(H_max − H_min), and the constants c are universal (p. 10) (reading R1)
--   - encoding: the simulated annealing algorithm with inverse temperature gap c/N, started uniformly → schedule β_j = min(jc/N, β), j = 1, …, ⌈βN/c⌉, m steps of OAI.CriticalSK.discreteKernel (β_j • W) each, from the uniform law; µ̂ is the exact law of the output; reason: every gap is ≤ c/N, the schedule increases strictly from 0 and ends at β_L = β (checked in the verification file); at β = 0 there are no stages (reading R2)
--   - encoding: with probability at least 1 − N^{−a} → for every N ≥ N₀, the measure of {W : d_TV(µ̂, µ_{βW}) > N^{−a}} is ≤ N^{−a} (constant 1 kept); reason: the claim is asymptotic in N; written as a bound on the bad set (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.1, p. 1 (PDF p. 3); proof, p. 13

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf
import Definitions.Def_SKAnnealing_Sampling_annealRun

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Theorem 1.1.** Let `0 ≤ β < 1` and let `a > 0` be a (large) constant. With probability at least `1 − N^{−a}`
over `W ∼ GOE(N)`, the output distribution `µ̂` of the simulated annealing algorithm run for `O_{a,β}(N log N)` steps
of the Glauber dynamics per iteration, with inverse temperature gap `c/N`, run on the SK model `µ_{βW}`, is such that
`d_TV(µ̂, µ_{βW}) ≤ N^{−a}`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.1, p. 1 (PDF p. 3).

**Formalization Note** `µ_{βW} = gibbs (β • W)` (`hamiltonian W = ½⟨σ, Wσ⟩`, zero diagonal, R8), `W` drawn from
`disorderLaw N` (GOE off the diagonal), and `µ̂ = annealOutput W β c m` is the exact law of the run (R2: schedule
`β_j = min(jc/N, β)`, `j = 1, …, ⌈βN/c⌉`, `m` steps of `discreteKernel` per temperature, uniform start). Reading R1:
`c₀ > 0` is universal and the claim holds for every gap `c ∈ (0, c₀]` and every `m ≥ C N log N`; `C`, `N₀` depend on
`β, a, c`. The probability is over `W` only, written as the bad-set bound `≤ N^{−a}` (constant `1`); `N ≥ N₀` (R4). -/
theorem simulated_annealing_samples :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ a : ℝ, 0 < a → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ m : ℕ, C * N * Real.log N ≤ m →
        disorderLaw N {W | (N : ℝ) ^ (-a) < totalVariation (β • W) (annealOutput W β c m)}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
