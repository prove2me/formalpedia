-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_1_5
-- name    : SKAnnealing.Sampling.lemma_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:27.450076+00:00
-- url     : https://prove2.me/theorems/c217914b-6600-40e3-9eff-83372bcb8004
-- title:
--   Lemma 1.5, p. 4 — for large $T$, $\mu_T$ has Poincaré constant $O(N)$ with probability $1-e^{-cN}$
-- statement:
--   Let $0\le\beta<1$, $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$, $g\sim\mathcal N(0,\mathrm{Id})$ independently, and let $\mu_T$ be the measure obtained by running stochastic localization for time $T$ on the planted model $\mu_{\beta W+\frac{\beta^2}Nxx^\top}$:
--   $$\mu_T(y)\propto\exp\Big(\frac\beta2\,y^\top\Big(W+\beta\frac{xx^\top}N\Big)y+\big\langle Tx+g\sqrt T,\,y\big\rangle\Big).$$
--
--   **Lemma 1.5 ([BER26]).** There is $T_0>0$ such that for every $T\ge T_0$ there are constants $c>0$, $C>0$ and $N_0$ with, for all $N\ge N_0$,
--   $$\Pr\big[\mu_T\text{ does not satisfy a Poincaré inequality with constant }C N\big]\le e^{-cN}.$$
--
--   This supplies the second hypothesis of Lemma 2.4: the end point of the localization path is a measure on which Glauber dynamics has spectral gap of order $1/N$.
--
--   Differences from the source:
--   - reading: the range of β (unstated in Lemma 1.5) → 0 ≤ β < 1; reason: the paper's regime; never the weaker reading (at β = 0, µ_T is a product measure and satisfies the Poincaré inequality with constant N)
--   - reading: for a sufficiently large (constant) T → ∃ T₀ > 0, ∀ T ≥ T₀; c and C may depend on β and T; reason: the stronger reading of "sufficiently large" (reading R10, R3)
--   - encoding: stochastic localization on µ_{βW + (β²/N)xxᵀ} for time T → µ_T = tilt(µ_{βM}, T x + √T g) with g ∼ N(0, Id); reason: the plant replaces the localized sample (p. 12) and B_T has the law of √T g (readings R6, R11)
--   - reading: the standard Dirichlet form ℰ(f, f) and ‖f‖_∞ in display (2) → ℰ(f, f) = N^{−1} Σ_i E_µ[(f − P_i f)²] (the discrete Glauber chain of Definition 2.1), ‖f‖_∞ the maximum of |f| on the support of µ; reason: the (O(N), ·) constants fit the discrete-time chain; on the full-support Gibbs laws of the paper the support is all of {±1}^N (reading R7)
--   - encoding: with probability 1 − e^{−cN} → for every N ≥ N₀, the failure event has measure ≤ e^{−cN}; reason: the bound is asymptotic in N; written as a bound on the bad set (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 1.5, p. 4 (PDF p. 6); restated p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_IsWeakPoincare
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 1.5** ([BER26]). Let `µ_T` be the measure obtained by running stochastic localization on
`µ_{βW + (β²/N) xxᵀ}` for bounded time `T > 0`. Then, for a sufficiently large (constant) `T`, with probability
`1 − e^{−cN}`, `µ_T` has Poincaré constant `O(N)`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 1.5, p. 4 (PDF p. 6); restated p. 33 (PDF p. 35).

**Formalization Note** Reading R11: `µ_T = plantedTilted β T W x g` (localized sample = plant `x`, `B_T = √T g`).
Reading R10: "sufficiently large `T`" is `∃ T₀ > 0, ∀ T ≥ T₀`; `c`, `C` may depend on `β`, `T` (R3). The Poincaré
constant is for the Glauber Dirichlet form (R7). `0 ≤ β < 1` (reading: no range is printed; the paper's regime). -/
theorem lemma_1_5 :
    ∀ β : ℝ, 0 ≤ β → β < 1 → ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        plantedFieldLaw N {ω | ¬ IsPoincare (plantedTilted β T ω.1.1 ω.1.2 ω.2) (C * N)}
          ≤ ENNReal.ofReal (Real.exp (-(c * N))) := by sorry

end SKAnnealing.Sampling
