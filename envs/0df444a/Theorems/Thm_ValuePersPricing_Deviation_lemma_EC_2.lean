-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_EC_2
-- name    : ValuePersPricing.Deviation.lemma_EC_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:52.291985+00:00
-- url     : https://prove2.me/theorems/a838575d-6ddd-4908-8447-db000fd02cd2
-- title:
--   Lemma EC.2, p. ec3 — strongest bound by regime: sign patterns and unique roots at δL and δM
-- statement:
--   Let $S>1$ and let $\delta_L,\delta_M,\delta_H$ be the thresholds at $M=1$:
--   $$\delta_L=\frac{\log S}{-W_{-1}(-1/(eS))},\qquad \delta_M=\frac{\log S}{1+\log S},\qquad \delta_H=\frac{S-1}{S}.$$
--
--   1. The function
--   $$f(D)=\frac{-W_{-1}\big(-\frac{1-D}{e}\big)}{1-D}-\frac{\log S}{D}$$
--   is negative for $D\in(0,\delta_L)$, positive for $D\in(\delta_L,\delta_H]$, and $\delta_L$ is its unique root in $(0,\delta_H]$.
--   2. The function
--   $$g(D)=\frac{\log S}{D}+W_{-1}\Big(\frac{-1}{eS(1-D)}\Big)$$
--   vanishes at $D=\delta_M$, is non-negative for all $D\in(0,\delta_H]$, and $\delta_M$ is its unique root in $(0,\delta_H]$.
--
--   Consequently, in the standardized case, the low bound (EC.5) is the strongest on $[0,\delta_L]$, the medium bound (EC.6) on $(\delta_L,\delta_M]$, and the high bound (EC.7) on $(\delta_M,\delta_H]$.
--
--   Differences from the source:
--   - encoding: (b) "non-negative for all D ∈ [0, δH]" → for D ∈ (0, δH]; reason: log(S)/D is undefined at D = 0.
--   - encoding: no hypothesis on S → 1 < S; reason: the lemma sits inside the proof of Theorem 2, whose standing hypothesis is S > 1; for S = 1 all thresholds are 0 and log S = 0.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. ec3 (PDF 35), Lemma EC.2; proof pp. ec6–ec7 (PDF 38–39)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma EC.2 (p. ec3), for `S > 1` with `δ_L, δ_M, δ_H` at `M = 1`:
(a) `f(D) = −W₋₁(−(1 − D)/e)/(1 − D) − log(S)/D` is negative on `(0, δ_L)`, positive on
`(δ_L, δ_H]`, and `δ_L` is its unique root in `(0, δ_H]`;
(b) `g(D) = log(S)/D + W₋₁(−1/(e S (1 − D)))` vanishes at `δ_M`, is non-negative on `(0, δ_H]`,
and `δ_M` is its unique root there. -/
theorem lemma_EC_2 (S : ℝ) (hS : 1 < S) :
    ((∀ D ∈ Ioo 0 (deltaL 1 S),
        -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D < 0) ∧
      (∀ D ∈ Ioc (deltaL 1 S) (deltaH 1 S),
        0 < -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D) ∧
      -lambertWm1 (-(1 - deltaL 1 S) / Real.exp 1) / (1 - deltaL 1 S)
          - Real.log S / deltaL 1 S = 0 ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        -lambertWm1 (-(1 - D) / Real.exp 1) / (1 - D) - Real.log S / D = 0 →
          D = deltaL 1 S)) ∧
    (Real.log S / deltaM 1 S
          + lambertWm1 (-1 / (Real.exp 1 * S * (1 - deltaM 1 S))) = 0 ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        0 ≤ Real.log S / D + lambertWm1 (-1 / (Real.exp 1 * S * (1 - D)))) ∧
      (∀ D ∈ Ioc 0 (deltaH 1 S),
        Real.log S / D + lambertWm1 (-1 / (Real.exp 1 * S * (1 - D))) = 0 →
          D = deltaM 1 S)) := by sorry

end ValuePersPricing.Deviation
