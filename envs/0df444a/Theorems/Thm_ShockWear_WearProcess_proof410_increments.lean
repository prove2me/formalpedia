-- Prove2me | Theorems.Thm_ShockWear_WearProcess_proof410_increments
-- name    : ShockWear.WearProcess.proof410_increments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:55:29.372448+00:00
-- url     : https://prove2.me/theorems/ad349ef9-b63e-4f7a-a592-056a7c9735df
-- title:
--   Proof of Theorem 4.10 (p. 641) — the grid increments of a Markov wear process satisfy (4.3)–(4.5)
-- statement:
--   Let $\{Z(t),t\ge0\}$ satisfy (4.8), (4.9) and (4.10): almost every path starts at $0$ and is nondecreasing, the process is Markov for its natural filtration, and a version of $P\{Z(t+\Delta)-Z(t)\le u\mid Z(t)=z\}$ is decreasing in both $z$ and $t$ for $t\ge0$, $z\ge0$, $\Delta\ge0$. Fix $\Delta>0$ and put
--
--   $$
--   X_i=Z(i\Delta)-Z((i-1)\Delta),\qquad i=1,2,\dots .
--   $$
--
--   Then $X_1,X_2,\dots$ are nonnegative random variables satisfying the conditions (4.3), (4.4) and (4.5) of Lemma 4.1b, for some choice of versions $\kappa'_k$ of the conditional laws of $X_{k+1}$ given $Z_k=X_1+\dots+X_k$.
--
--   This is the reduction of the continuous-time problem to the discrete dependent-damage model: the Markov property (4.9) gives (4.3), and the two monotonicities in (4.10) give (4.4) and (4.5).
--
--   **Formalization Note** The conclusion is `∃ κ', IsDamageSeq pr X κ'`; nonnegativity in `IsDamageSeq` is almost sure, which is what (4.8) provides. Lean's `wearIncr Z Δ i` is the paper's $X_{i+1}=Z((i+1)\Delta)-Z(i\Delta)$.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), p. 641, proof of Theorem 4.10, first sentence after "Choose Δ > 0" (up to "Lemma 4.1b")

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ShockWear.WearProcess

theorem proof410_increments {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (κ : ℝ≥0 → ℝ≥0 → Kernel ℝ ℝ)
    (hZ : IsWearProcess pr Z κ) (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    ∃ κ' : ℕ → Kernel ℝ ℝ, IsDamageSeq pr (wearIncr Z Δ) κ' := by sorry

end ShockWear.WearProcess
