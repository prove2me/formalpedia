-- Prove2me | Theorems.Thm_TamedEuler_Convergence_lemma_3_6
-- name    : TamedEuler.Convergence.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:52.934406+00:00
-- url     : https://prove2.me/theorems/4b12a870-9640-4008-8a6d-71b5cc9274e1
-- title:
--   Lemma 3.6, p. 16 — sup_N N^p · ℙ[(Ω^N_N)^c] < ∞
-- statement:
--   In the standing setting of p. 2, let $\Omega^N_N$ be the events (14). Then
--   $$\sup_{N\in\mathbb N}\big(N^p\cdot\mathbb P[(\Omega^N_N)^c]\big)<\infty$$
--   for all $p\in[1,\infty)$.
--
--   The bad events, where the dominator lemma gives no control, have probability decaying faster than any power of $N$; on them a cruder bound on the scheme suffices.
--
--   **Formalization Note** $N^p\,\mathbb P[\cdot]$ is computed in $[0,\infty]$; for each $p\ge1$ one finite constant bounds it for every $N\ge1$.
-- source:
--   Hutzenthaler, Jentzen, Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.6, (32)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_TamedEuler_Convergence_Setting
import Definitions.Def_TamedEuler_Convergence_Scheme
import Definitions.Def_TamedEuler_Convergence_Dominator

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TamedEuler.Convergence

open EthierKurtz

/-- Hutzenthaler–Jentzen–Kloeden, arXiv:1010.3756v2, p. 16, Lemma 3.6 (Estimation of the
probability of the complement of `Ω^N_N`), (32): `sup_{N ∈ ℕ} (N^p · ℙ[(Ω^N_N)^c]) < ∞` for
all `p ∈ [1, ∞)`. -/
theorem lemma_3_6 {d m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (c : ℝ)
    (W : ℝ≥0 → Ω → SDEState m) (ξ : Ω → SDEState d) (mu : SDEState d → SDEState d)
    (σ : SDEState d → Matrix (Fin d) (Fin m) ℝ)
    (h : Setting P ℱ T c W ξ mu σ) :
    ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ N : ℕ, 1 ≤ N →
      (N : ℝ≥0∞) ^ p * P (Good T c mu σ ξ W N N)ᶜ ≤ C := by sorry

end TamedEuler.Convergence
