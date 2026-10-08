-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_theorem_1_8
-- name    : SolomonRWRE.Speed.theorem_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:22.166503+00:00
-- url     : https://prove2.me/theorems/107716ac-d158-4e79-90a8-7d470fe76225
-- title:
--   Theorem (1.8) — stationary ergodic ladder times
-- statement:
--   Suppose the annealed walk satisfies $\limsup_{n\to\infty}X_n=+\infty$ almost surely. Then every positive ladder time $\tau_n=T_n-T_{n-1}$ is finite almost surely, and the entire sequence $(\tau_n)_{n\ge1}$ is strictly stationary and ergodic.
--
--   $$
--   P(\tau_n<\infty)=1\quad(n\ge1),\qquad
--   \mathcal L((\tau_{n+1})_{n\ge0})\text{ is ergodic under the left shift.}
--   $$
--
--   This gives the stationary process to which an ergodic theorem can be applied when studying passage times.
--
--   **Formalization Note** Mathlib's ergodicity predicate includes preservation of the full sequence law by the shift, which states strict stationarity.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 5, Theorem (1.8)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 5, Theorem (1.8). The complete joint law of the
ladder-time sequence is stationary and ergodic; every member is finite a.e. -/
theorem theorem_1_8 {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (h : SolomonRWRE.Recurrence.IsRWRE P α X)
    (hlim : ∀ᵐ ω ∂P, ∀ M : ℤ, ∃ᶠ n in Filter.atTop, M ≤ X n ω) :
    (∀ n : ℕ, ∀ᵐ ω ∂P, ladderTime X (n + 1) ω ≠ ⊤) ∧
      IsStationaryErgodic P X := by sorry

end SolomonRWRE.Speed
