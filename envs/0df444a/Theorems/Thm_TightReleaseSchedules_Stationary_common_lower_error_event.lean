-- Prove2me | Theorems.Thm_TightReleaseSchedules_Stationary_common_lower_error_event
-- name    : TightReleaseSchedules.Stationary.common_lower_error_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:46:41.011484+00:00
-- url     : https://prove2.me/theorems/dae1304a-a9bb-4b1e-9cef-5cf8f3698587
-- title:
--   Lemma 4.2 — A common lower-error event for adaptive releases
-- statement:
--   Fix $T,d\ge1$, a coordinate block $S$ of size $d_h\ge1$, and $0<\Delta\le1$. Let $\kappa=2^{-10}$, $\ell_0=\lceil\log_2(16d_h/\Delta^2)\rceil$ and $a_\ell=\sqrt{\kappa2^{-\ell}}$. Choose an integer $L\ge\ell_0$ with $2^L\ge T$, draw independent $U_\ell$ uniformly on $[-1,1]^S$, and set $H=\sum_{\ell=\ell_0}^La_\ell U_\ell$. Let $g_{1:T}$ be any deterministic path whose block projection equals a fixed $g_S$. Observations have target $g_t+H$ and independent Gaussian designs and unit Gaussian noise; the independent seed has any measurable probability law. Then:
--
--   1. Every cube realization satisfies $\|H\|_2<\Delta/32$.
--   2. For every $\ell_0\le\ell\le L$, every integer $0\le n\le\min\{2^\ell,T\}$ and every estimate $\widehat w$ measurable with respect to the seed and the first $n$ observations,
--
--   $$
--   \Pr\!\left\{\|P_S\widehat w-g_S-H\|_2\le\frac{a_\ell\sqrt{d_h}}{16}\right\}\le(9/25)^{d_h}.
--   $$
--
--   3. For every policy with at most $B$ releases, there exists a measurable event $E$, depending on that policy, with probability at least $1-B(L-\ell_0+1)(9/25)^{d_h}$, on which every actual release $(\tau_j,w^{(j)})$ with $\tau_j<T$ satisfies
--
--   $$
--   \|P_Sw^{(j)}-g_S-H\|_2^2\ge\frac{2^{-19}d_h}{\max\{\tau_j,16d_h/\Delta^2\}}.
--   $$
--
--   The event is common to all releases of the fixed policy, including time-zero releases. Neither dates nor their number are fixed in advance. This lemma treats adaptive estimation with a hidden stationary block and places no global norm or drift restriction on $g$.
--
--   Differences from the source:
--   - encoding: uniform cube levels and a pointwise support assertion → products of closed-interval subtypes indexed by signed integer levels; reason: the same uniform law is supported pointwise, including all boundary realizations
--   - encoding: arbitrary independent policy seed and observation filtration → an arbitrary measurable seed space with product law and the comap of the observed transcript filtration; reason: all source causal randomized rules and all observation-measurable estimates are included without revealing H
--   - encoding: nonnegative integer n and decimal 0.36, with a possibly negative event lower bound → n is natural, 0.36 is exactly 9/25, and probabilities use ENNReal.ofReal; reason: all nonnegative integers are covered and clipping a negative probability threshold to zero is equivalent
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Lemma 4.2, printed p.10, PDF p.11; proof continues printed p.11, PDF p.12

import Definitions.Def_TightReleaseSchedules_Stationary_multiscale_prior

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace TightReleaseSchedules.Stationary

/-- Lemma 4.2, with an arbitrary independent seed and the explicit cube-product prior. -/
theorem common_lower_error_event (T d : ℕ) (hT : 0 < T) (hd : 0 < d)
    (S : Finset (Fin d)) (hS : 0 < S.card) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1)
    (L : ℤ) (hL : firstLevel S.card Δ ≤ L) (hLT : (T : ℝ) ≤ (2 : ℝ) ^ L)
    (g : Fin T → Vector d) (gS : BlockVector S)
    (hg : ∀ i, blockProjection S (g i) = gS) (s : RandomSeed) :
    (∀ u : PriorDraws S Δ L, ‖hiddenShift S Δ L u‖ < Δ / 32) ∧
    (∀ ℓ : ℤ, firstLevel S.card Δ ≤ ℓ → ℓ ≤ L →
      ∀ n : ℕ, n ≤ T → (n : ℝ) ≤ (2 : ℝ) ^ ℓ →
      ∀ ŵ : PriorSample s T d S Δ L → Vector d,
        @Measurable _ _ (priorInformation g n) inferInstance ŵ →
        priorLaw s T d S Δ L {ω |
          ‖blockProjection S (ŵ ω) - gS - hiddenShift S Δ L ω.2.1‖ ≤
            levelAmplitude ℓ * Real.sqrt S.card / 16} ≤
          ENNReal.ofReal ((9 / 25 : ℝ) ^ S.card)) ∧
    (∀ B : ℕ, ∀ π : ReleasePolicy s T d B, IsCausal π →
      ∃ E : Set (PriorSample s T d S Δ L), MeasurableSet E ∧
        ENNReal.ofReal (1 - (B : ℝ) * ((L - firstLevel S.card Δ + 1 : ℤ) : ℝ) *
          (9 / 25 : ℝ) ^ S.card) ≤ priorLaw s T d S Δ L E ∧
        ∀ ω ∈ E, ∀ j : Fin B, π.date j (priorTranscript g ω) < T →
          (2 : ℝ) ^ (-19 : ℤ) * S.card /
            max (π.date j (priorTranscript g ω) : ℝ) (16 * S.card / Δ ^ 2) ≤
          ‖blockProjection S (π.head j (priorTranscript g ω)) - gS -
            hiddenShift S Δ L ω.2.1‖ ^ 2) := by sorry

end TightReleaseSchedules.Stationary
