-- Prove2me | Theorems.Thm_ShockWear_WearProcess_proof410_all_times
-- name    : ShockWear.WearProcess.proof410_all_times
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:55:54.617851+00:00
-- url     : https://prove2.me/theorems/93d54bc1-f619-4f16-af00-59a57d5d5d37
-- title:
--   Proof of Theorem 4.10 (p. 641) — $[F_s(x)]^{1/s}\ge[F_t(x)]^{1/t}$ whenever $0<s\le t$
-- statement:
--   Let $\{Z(t),t\ge0\}$ satisfy (4.8), (4.9) and (4.10), and let $F_t(x)=P\{Z(t)\le x\}$. Then for every real $x$ and all times $0<s\le t$,
--
--   $$
--   \big[F_s(x)\big]^{1/s}\ \ge\ \big[F_t(x)\big]^{1/t}.
--   $$
--
--   The paper first obtains this for $s/t$ rational from the grid statement and then for all $s<t$; the item states the final form, for all $0<s\le t$. In words, $t\mapsto[P\{Z(t)\le x\}]^{1/t}$ is decreasing on $t>0$.
--
--   **Formalization Note** Times are nonnegative reals and the exponents $1/s$, $1/t$ are real.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 641, proof of Theorem 4.10, sentences "This means that … rational multiples of s"

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_all_times {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (x : ℝ) (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t) :
    wearCdf pr Z t x ^ (1 / (t : ℝ)) ≤ wearCdf pr Z s x ^ (1 / (s : ℝ)) := by sorry

end ShockWear.WearProcess
