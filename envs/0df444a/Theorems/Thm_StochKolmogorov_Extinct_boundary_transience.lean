-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_boundary_transience
-- name    : StochKolmogorov.Extinct.boundary_transience
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:14.131171+00:00
-- url     : https://prove2.me/theorems/e90101de-a4c8-45b4-9f11-d4720871678d
-- title:
--   §5, p. 24 — transience in the interior
-- statement:
--   Under Assumptions 1.1 and 1.3, the process is transient in the strictly positive orthant in the sense used in the proof: for each compact set $K$ with nonempty interior inside the positive orthant, some interior state $x$ has positive probability of never hitting $K$. Thus
--
--   $$\mathbb P_x\{\exists t\ge0:X(t)\in K\}<1.$$
--
--   This rules out recurrence in the sense invoked just before the boundary-limit argument.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §5, proof of Theorem 5.1, p. 24, paragraph beginning “We show by contradiction”

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem boundary_transience {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu) :
    ∀ K : Set (SDEState n), IsCompact K → (interior K).Nonempty →
      K ⊆ openOrthant n →
      ∃ x ∈ openOrthant n, P {ω | ∃ t : ℝ≥0, X x t ω ∈ K} < 1 := by sorry

end StochKolmogorov.Extinct
