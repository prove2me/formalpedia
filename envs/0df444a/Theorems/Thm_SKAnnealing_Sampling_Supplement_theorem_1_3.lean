-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_Supplement_theorem_1_3
-- name    : SKAnnealing.Sampling.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:49:45.998934+00:00
-- url     : https://prove2.me/theorems/f86e3640-eb07-4a8d-8b64-bf43fc70e497
-- title:
--   Theorem 1.3, p. 2 — zero-field SK covariance bound $\mathbf{Cov}(\mu_{\beta W})\preceq L_{\beta,a}\,\mathrm{Id}$ with probability $\ge 1-N^{-a}$, all $0<\beta<1$
-- statement:
--   Let $W\sim\mathrm{GOE}(N)$, i.e. $W_{ij}=W_{ji}\sim\mathcal N(0,\tfrac1N)$, and let $\mu_{\beta W}$ be the Sherrington–Kirkpatrick Gibbs measure on $\{\pm1\}^N$,
--   $$\mu_{\beta W}(\sigma)\propto\exp\Big(\frac\beta2\,\langle\sigma,W\sigma\rangle\Big).$$
--   Write $\mathbf{Cov}(\mu_{\beta W})$ for the $N\times N$ covariance matrix of the spins, $\mathbf{Cov}_{ij}=\mathbf E[\sigma_i\sigma_j]-\mathbf E[\sigma_i]\,\mathbf E[\sigma_j]$, and $\preceq$ for the Loewner order on symmetric matrices.
--
--   **Theorem 1.3.** Let $0<\beta<1$ and $a>0$. There is a constant $L=L_{\beta,a}$, depending only on $\beta$ and $a$, such that for every $N$,
--   $$\Pr_{W\sim\mathrm{GOE}(N)}\Big[\mathbf{Cov}(\mu_{\beta W})\preceq L\cdot\mathrm{Id}\Big]\ge 1-N^{-a}.$$
--
--   This is the high-probability covariance bound for the zero-field SK model throughout the high-temperature phase: with probability $1-N^{-a}$ the Gibbs measure has spectrally bounded covariance, uniformly in $N$. It is the special case, without planted spike and external field, of the analysis behind Theorem 1.4.
--
--   **Formalization Note** $\mu_{\beta W}$ is the published `OAI.CriticalSK.gibbs (β • W)`, whose Hamiltonian $\sum_{i<k}W_{ik}\sigma_i\sigma_k$ equals $\tfrac12\langle\sigma,W\sigma\rangle$; $W$ is drawn from `OAI.CriticalSK.disorderLaw N` and $\mathbf{Cov}$ is `OAI.CriticalSK.covariance`. The Loewner bound is that $L\cdot\mathrm{Id}-\mathbf{Cov}$ is positive semidefinite, and the probability is written as the bound $N^{-a}$ on the measure of the failure set.
--
--   Differences from the source:
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure or covariance (the paper says so on p. 13; base reading R8)
--   - encoding: with probability at least 1 − N^{−a}, Cov(µ_{βW}) ⪯ L · Id → the measure of {W : L·1 − Cov(µ_{βW}) is not positive semidefinite} is ≤ N^{−a} (constant 1 kept), for every N; reason: the complement of the good event, written as a bound on the bad set; same instances
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.3, p. 2 (PDF p. 4); restated p. 13 (PDF p. 15); model (1), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_CriticalSK

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling.Supplement

/-- **Theorem 1.3.** Let `0 < β < 1` and `a > 0`. Then, for some bounded constant `L = L_{β,a}`, with probability
at least `1 − N^{−a}` over `W ∼ GOE(N)`, the SK model (1) is such that `Cov(µ_{βW}) ⪯ L · Id`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.3, p. 2 (PDF p. 4); restated p. 13 (PDF p. 15).

**Formalization Note** `µ_{βW} = gibbs (β • W)`: `hamiltonian W σ = ∑_{i<k} W_ik σ_i σ_k = ½⟨σ, Wσ⟩` for the symmetric
matrix with zero diagonal, and `W` is drawn from `disorderLaw N` (off-diagonal entries iid `N(0, 1/N)`). The
diagonal of `W` is absent: `σ_i² = 1`, so it changes no Gibbs measure and no covariance (the paper says so on
p. 13; reading R8 of the base mission). `Cov(µ_{βW}) = covariance (β • W)`, the spin covariance matrix, and
`⪯` is the Loewner order, i.e. `L • 1 − Cov` is positive semidefinite. `L` depends only on `β` and `a`; the
claim holds for every `N`, and the probability is written as the bound `≤ N^{−a}` (constant `1`) on the
measure of the failure set. -/
theorem theorem_1_3 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ a : ℝ, 0 < a →
      ∃ L : ℝ, ∀ N : ℕ,
        disorderLaw N {W | ¬ (L • (1 : Matrix (Fin N) (Fin N) ℝ) - OAI.CriticalSK.covariance (β • W)).PosSemidef}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling.Supplement
