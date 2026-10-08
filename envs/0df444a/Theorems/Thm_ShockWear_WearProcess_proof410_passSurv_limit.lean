-- Prove2me | Theorems.Thm_ShockWear_WearProcess_proof410_passSurv_limit
-- name    : ShockWear.WearProcess.proof410_passSurv_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:56:03.909078+00:00
-- url     : https://prove2.me/theorems/c5b9269a-fe92-4e60-8220-be0c5fd31526
-- title:
--   Proof of Theorem 4.10 (p. 641) — $\bar H_x(t)=\lim_{\varepsilon\downarrow0}F_{t+\varepsilon}(x)$
-- statement:
--   Let $\{Z(t),t\ge0\}$ satisfy (4.8): every $Z(t)$ is a random variable and almost every sample path starts at $0$ and is nondecreasing. Let $T_x=\inf\{t\ge0:Z(t)>x\}\in[0,\infty]$ be the first passage time above the level $x$, $\bar H_x(t)=P\{T_x>t\}$ its survival function, and $F_t(x)=P\{Z(t)\le x\}$. Then for every real $x$ and every $t\ge0$,
--
--   $$
--   \bar H_x(t)=\lim_{\varepsilon\to0^+}F_{t+\varepsilon}(x).
--   $$
--
--   The paper derives it from the pathwise equivalence "$T_x>t$ if and only if $Z(t+\varepsilon)\le x$ for some $\varepsilon>0$". It transfers the inequality for the wear distributions to the first passage time.
--
--   **Formalization Note** Only (4.8) is assumed (the Markov conditions are not needed for this step); the limit is taken from the right, $\varepsilon\downarrow0$ with $\varepsilon>0$. $T_x$ may be infinite with positive probability.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 641, proof of Theorem 4.10, sentence "Since T_x > t if and only if …"

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_passSurv_limit {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (hZ : IsMonotoneWear pr Z) (x : ℝ) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ≥0 => wearCdf pr Z (t + ε) x) (𝓝[>] 0)
      (𝓝 (passSurv pr Z x (t : ℝ))) := by sorry

end ShockWear.WearProcess
