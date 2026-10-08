-- Prove2me | Theorems.Thm_ShockWear_WearProcess_proof410_grid
-- name    : ShockWear.WearProcess.proof410_grid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:55:46.639041+00:00
-- url     : https://prove2.me/theorems/9b50de8f-68d8-44c3-9d18-db2b3a762cb6
-- title:
--   Proof of Theorem 4.10 (p. 641) — $[F_{k\Delta}(x)]^{1/(k\Delta)}$ is decreasing in $k=1,2,\dots$
-- statement:
--   Let $\{Z(t),t\ge0\}$ satisfy (4.8), (4.9) and (4.10), and let $F_t(x)=P\{Z(t)\le x\}$ be the distribution function of the wear at time $t$. Then for every $\Delta>0$ and every real $x$,
--
--   $$
--   \big[F_{k\Delta}(x)\big]^{1/(k\Delta)}\quad\text{is decreasing in } k=1,2,\dots .
--   $$
--
--   This is the statement of the IHRA property along the grid $\Delta,2\Delta,3\Delta,\dots$, obtained from Lemma 4.1b applied to the grid increments.
--
--   **Formalization Note** The exponent $1/(k\Delta)$ is a real number; the statement is $[F_{k\Delta}(x)]^{1/(k\Delta)}\le[F_{j\Delta}(x)]^{1/(j\Delta)}$ for $1\le j\le k$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 641, proof of Theorem 4.10, first display

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_grid {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) (hΔ : 0 < Δ) (x : ℝ) (j k : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    wearCdf pr Z (k • Δ) x ^ (1 / ((k : ℝ) * (Δ : ℝ))) ≤
      wearCdf pr Z (j • Δ) x ^ (1 / ((j : ℝ) * (Δ : ℝ))) := by sorry

end ShockWear.WearProcess
