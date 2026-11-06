-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_theorem_1_4
-- name    : SKAnnealing.Sampling.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:45.562372+00:00
-- url     : https://prove2.me/theorems/100ec74e-ad74-4d73-8f76-088b8f525f78
-- title:
--   Theorem 1.4, p. 4 — $\|\mathbf{Cov}(\mu_t)\|\le L$ with probability $1-O(N^{-a})$ for the planted SK model with field $tx+g\sqrt t$
-- statement:
--   Let $0<\beta<1$ and let $a>0$ be a (large) constant. Draw $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$ and $g\sim\mathcal N(0,\mathrm{Id})$ independently, and for $t>0$ let $\mu_t$ be the probability measure on $\{\pm1\}^N$ with
--   $$\mu_t(y)\propto\exp\Big(\frac\beta2\,y^\top\Big(W+\beta\frac{xx^\top}N\Big)y+\big\langle tx+g\sqrt t,\,y\big\rangle\Big).$$
--
--   **Theorem 1.4.** For every $T>0$ there are constants $L$, $C$ and $N_0$ such that for all $N\ge N_0$ and every $t\in(0,T]$,
--   $$\Pr\big[\|\mathbf{Cov}(\mu_t)\|_{\mathrm{op}}>L\big]\le C\,N^{-a}.$$
--
--   This is the main technical result of the paper: a covariance bound, uniform in $N$, for the planted SK model along the stochastic localization path. Via display (7), Lemma 2.4 and Lemma 2.5 it yields the weak Poincaré inequality of Theorem 1.2.
--
--   Differences from the source:
--   - reading: fix t > 0 bounded, possibly decaying with N → one N₀ and one constant serve every t ∈ (0, T], for every T > 0; reason: a bound uniform over t ∈ (0, T] is equivalent to the bound for every sequence t_N ∈ (0, T], which is what "possibly decaying with N" requires (reading R5)
--   - reading: L = L_{β,a} → L may also depend on the bound T on t; reason: "Fix t > 0 bounded": the constant may depend on the statement's fixed parameters, which include the bound on t (reading R3)
--   - encoding: with probability 1 − O(N^{−a}), ∥Cov(µ_t)∥ ⩽ L → ∃ C, N₀ such that for every N ≥ N₀ the measure of the failure event is ≤ C·N^{−a}; reason: O(·) is a constant; the probability is written as the bound on the bad set (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.4, p. 4 (PDF p. 6); restated pp. 12, 15

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Theorem 1.4.** Let `0 < β < 1` and `a > 0`. Fix `t > 0` bounded, possibly decaying with `N`. For
`g ∼ N(0, Id)` and `x ∼ Unif{±1}^N`, let `µ_t(y) ∝ exp((β/2) yᵀ(W + β xxᵀ/N) y + ⟨t x + g √t, y⟩)`. Then there
is a constant `L = L_{β,a}` such that with probability `1 − O(N^{−a})`, `‖Cov(µ_t)‖ ≤ L`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.4, p. 4 (PDF p. 6); restated pp. 12, 15.

**Formalization Note** `W ∼ GOE(N)` off the diagonal, `x`, `g` independent (`plantedFieldLaw`). Reading R5: uniformly
over `t ∈ (0, T]` for `N ≥ N₀`; `L` may depend on the bound `T` on `t` (R3). `O(N^{−a})` is `C N^{−a}` (R4).
`‖·‖` is the Euclidean operator norm. -/
theorem theorem_1_4 :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ a : ℝ, 0 < a → ∀ T : ℝ, 0 < T →
      ∃ L C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, 0 < t → t ≤ T →
        plantedFieldLaw N {ω | L < lawCovNorm (plantedTilted β t ω.1.1 ω.1.2 ω.2)}
          ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
