-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_display_7
-- name    : SKAnnealing.Sampling.display_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:30.264875+00:00
-- url     : https://prove2.me/theorems/bb877702-7704-42de-8ab0-64f5606b786e
-- title:
--   Display (7), p. 13 — $\sup_{t\le T}\|\mathbf{Cov}(\mu_t)\|_{\mathrm{op}}\le K$ along the localization path, with probability $1-O(N^{-a})$ in both layers
-- statement:
--   Let $0\le\beta<1$, $W\sim\mathrm{GOE}(N)$ and $x\sim\mathrm{Unif}\{\pm1\}^N$ independently, and let $\pi_{W,x}$ be the planted SK model with interaction $\beta(W+\frac\beta Nxx^\top)$. Given $(W,x)$, let $(B_t)_{t\ge0}$ be a standard Brownian motion in $\mathbb R^N$ and run stochastic localization on $\pi_{W,x}$ with the plant as the localized sample:
--   $$\mu_t(y)\propto\pi_{W,x}(y)\,\exp\langle tx+B_t,\,y\rangle .$$
--
--   **Display (7).** For every $T>0$ and every constant $a>0$ there are constants $K$, $C$ and $N_0$ such that for all $N\ge N_0$ and every probability space carrying such a Brownian motion,
--   $$\Pr_{W,x}\Big[\ \Pr_{B}\Big[\sup_{0\le t\le T}\|\mathbf{Cov}(\mu_t)\|_{\mathrm{op}}>K\Big]>C\,N^{-a}\Big]\le C\,N^{-a}.$$
--
--   This is the "stronger version of Theorem 1.4" proved inside the proof of Theorem 1.1: the covariance bound holds simultaneously along the whole localization path, which is the first hypothesis of Lemma 2.4.
--
--   Differences from the source:
--   - reading: the range of β (unstated in (7)) → 0 ≤ β < 1; reason: (7) is proved inside the proof of Theorem 1.1, which covers 0 ≤ β < 1; never the weaker reading (at β = 0 the path measures are product measures with ‖Cov‖ ≤ 1)
--   - reading: T (unstated) → every T > 0; reason: the stronger reading; the proof of Theorem 1.1 uses the T of Lemma 1.5
--   - encoding: (µ_t)_{t∈[0,T]} ∼ SL on the planted model → µ_t = tilt(π_{W,x}, t x + B_t) with the plant x as the localized sample and B a standard Brownian motion in ℝ^N; the inner probability is over B for fixed (W, x); reason: p. 12: (x, H_pl) has the same law as H_pl and then x ∼ µ_{βM}, so the plant can replace the sample (readings R6, R11)
--   - encoding: Pr[Pr[sup ⩽ K] ⩾ 1 − O(N^{−a})] ⩾ 1 − O(N^{−a}) → both layers as bad-set bounds ≤ C·N^{−a}, one C and one N₀ for both O(·); reason: O(·) is a constant and the probabilities are written as bounds on failure events (reading R4); taking the larger of two constants gives one
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), proof of Theorem 1.1, display (7), p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_IsStdBrownian
import Definitions.Def_SKAnnealing_Sampling_plantedTilted

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Display (7)** (the "stronger version of Theorem 1.4" in the proof of Theorem 1.1). For any constant
`a > 0`: `Pr_{W,x}[Pr_{(µ_t)_{t ∈ [0,T]} ∼ SL}[sup_{0 ≤ t ≤ T} ‖Cov(µ_t)‖_op ≤ K] ≥ 1 − O(N^{−a})] ≥ 1 − O(N^{−a})`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), proof of Theorem 1.1, display (7), p. 13 (PDF p. 15).

**Formalization Note** Readings R6, R11: the localization path is `µ_t = tilt(µ_{βM}, t x + B_t)` with the plant `x`
and a standard Brownian motion `B` in `ℝ^N` (any probability space carrying one); the inner probability is over
`B` for fixed `(W, x)`. Both probabilities are written as bad-set bounds `≤ C N^{−a}` (one `C` for both
`O(·)`s). `0 ≤ β < 1` (reading: the proof of Theorem 1.1 covers `β ∈ [0, 1)`), every `T > 0`, `N ≥ N₀`. -/
theorem display_7 :
    ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ T : ℝ≥0, 0 < T → ∀ a : ℝ, 0 < a →
      ∃ K C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : ℝ≥0 → Ω → (Fin N → ℝ)), IsStdBrownian B P →
          plantedLaw N {wx | ENNReal.ofReal (C * (N : ℝ) ^ (-a)) <
              P {ω | ∃ t : ℝ≥0, t ≤ T ∧
                K < lawCovNorm (tilt (gibbs (plantedDisorder β wx.1 wx.2))
                  ((t : ℝ) • spinVec wx.2 + B t ω))}}
            ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-a)) := by sorry

end SKAnnealing.Sampling
