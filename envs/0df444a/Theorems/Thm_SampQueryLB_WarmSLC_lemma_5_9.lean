-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_5_9
-- name    : SampQueryLB.WarmSLC.lemma_5_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:06.767547+00:00
-- url     : https://prove2.me/theorems/99b0e850-b2d5-44ff-b087-07403c65e3ec
-- title:
--   Lemma 5.9 — parameter bounds: $K\ge2(Q+1)^2$, $2(Q+1)e^{-Kr^2/(4(Q+1)^2)}\le\zeta<\frac12$, $Qr<P^{-1/2}$, $M\le n^2$, $e_h\le n^{-10}$
-- statement:
--   With the parameters of §5.4.1, $\zeta=e^{-Q^2}n^{-300}$, $r=\big(1204(Q+1)^2(Q^2+\log n)/K\big)^{1/2}$, $M=|\mathcal P|[Q(h+1)(d_n+1)+1]$, $\delta=\frac32\zeta M$, $e_0=\zeta$, $e_i=\zeta+2Q(e_{i-1}+\delta)$:
--
--   **Lemma 5.9.** For all sufficiently large $n$:
--   (i) $K\ge2(Q+1)^2$ and $2(Q+1)e^{-Kr^2/(4(Q+1)^2)}\le\zeta<\frac12$;
--   (ii) $Qr<P^{-1/2}$;
--   (iii) $M\le n^2$ and $e_h\le n^{-10}$.
--
--   These are the numerical facts that close the level induction of §5.4.
--
--   Differences from the source: none.
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 45, Lemma 5.9 (PDF p. 48)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_5_9 :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      (2 * (QQ n + 1) ^ 2 ≤ KK n ∧
        2 * ((QQ n : ℝ) + 1) * Real.exp (-((KK n : ℝ) * rP n ^ 2 / (4 * ((QQ n : ℝ) + 1) ^ 2))) ≤
          zetaP n ∧ zetaP n < 1 / 2) ∧
      (QQ n : ℝ) * rP n < (PP n : ℝ) ^ (-(1 / 2 : ℝ)) ∧
      (MP n ≤ n ^ 2 ∧ eP n (hh n) ≤ ((n : ℝ) ^ 10)⁻¹) := by sorry

end SampQueryLB.WarmSLC
